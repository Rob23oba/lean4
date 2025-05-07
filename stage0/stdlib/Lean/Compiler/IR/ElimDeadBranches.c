// Lean compiler output
// Module: Lean.Compiler.IR.ElimDeadBranches
// Imports: Lean.Compiler.IR.Format Lean.Compiler.IR.Basic Lean.Compiler.IR.CompilerM
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_IR_elimDeadBranches_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_UnreachableBranches_interpExpr_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_UnreachableBranches_updateJPParamsAssignment_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_Value_widening(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_containsCtor___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_UnreachableBranches_Value_beq___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_UnreachableBranches_inferStep_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_qsort_sort___at___Lean_IR_UnreachableBranches_initFn____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177__spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_formatArray___at___Lean_IR_UnreachableBranches_Value_format_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_Value_truncateMaxDepth;
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_Value_truncate_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_initFn___lam__1____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_updateVarAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_IR_UnreachableBranches_initFn____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177__spec__0___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_markJPVisited_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_IR_elimDeadBranches_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_foldM_loop___at___Lean_IR_UnreachableBranches_inferStep_spec__3___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_Value_beq___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_reprValue____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_43____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_Value_beq___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_elimDeadBranches___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_projValue(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_formatArray___at___Lean_IR_UnreachableBranches_Value_format_spec__0___boxed(lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_instToFormatValue;
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_Value_toFormat___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at___Lean_IR_elimDeadBranches_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instBEqVarId;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___Lean_IR_UnreachableBranches_findVarValue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_resetNestedJPParams(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_instInhabitedValue;
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_updateJPParamsAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___Lean_IR_UnreachableBranches_updateCurrFnSummary_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_markJPVisited_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_elimDeadBranches___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_UnreachableBranches_Value_beq___lam__1(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_elimDead(lean_object*, lean_object*);
uint8_t l_Lean_IR_FnBody_isTerminal(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__4___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Format_join(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT uint8_t l_Lean_IR_UnreachableBranches_Value_toFormat___lam__0(uint8_t, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___Lean_IR_UnreachableBranches_Value_beq_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at___Lean_IR_UnreachableBranches_Value_merge_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Format_joinSep(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___Lean_IR_UnreachableBranches_Value_truncate_go_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_IR_UnreachableBranches_initFn____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_instReprValue;
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at___Lean_IR_UnreachableBranches_Value_merge_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_UnreachableBranches_Value_truncate_go_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Environment_addExtraName(lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedFnBody;
lean_object* l_Lean_IR_instHashableVarId___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt;
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_reprValue____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_43__spec__0___redArg(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_IR_UnreachableBranches_Value_truncate_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_Value_instToString;
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_UnreachableBranches_inferStep_spec__3___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_projValue___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_Value_instToString___lam__0(lean_object*);
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_format___at___Lean_IR_UnreachableBranches_Value_format_spec__2(lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_CtorInfo_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_UnreachableBranches_interpFnBody_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_Value_format(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_UnreachableBranches_inferStep_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_UnreachableBranches_inferStep_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_elimDeadBranches(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_findArgValue___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___Lean_IR_UnreachableBranches_findVarValue_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_List_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_UnreachableBranches_Value_beq___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___Lean_IR_UnreachableBranches_Value_truncate_go_spec__2___boxed(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT uint8_t l_Lean_IR_UnreachableBranches_containsCtor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_reprValue____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_43__spec__0___boxed(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___Lean_IR_UnreachableBranches_Value_beq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Std_Format_joinSep___at___List_format___at___Lean_IR_UnreachableBranches_Value_format_spec__2_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_IR_UnreachableBranches_initFn____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177__spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_UnreachableBranches_updateJPParamsAssignment_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_declLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_UnreachableBranches_markJPVisited_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* l_Lean_IR_LocalContext_getJPParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_inferStep(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_Value_toFormat(lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_UnreachableBranches_inferStep_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_resetNestedJPParams_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_resetNestedJPParams_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_initFn___lam__2____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177_(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_markJPVisited(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_IR_UnreachableBranches_initFn____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177__spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at___Lean_IR_UnreachableBranches_Value_merge_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_Value_instBEq;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_IR_UnreachableBranches_updateCurrFnSummary_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_IR_UnreachableBranches_Value_toFormat_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_resetNestedJPParams___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at___Lean_IR_elimDeadBranches_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_instToStringValue;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_reprValue____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_43_(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___Lean_IR_UnreachableBranches_Value_beq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_IR_UnreachableBranches_updateCurrFnSummary_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_IR_UnreachableBranches_initFn____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_UnreachableBranches_Value_addChoice_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_IR_UnreachableBranches_Value_toFormat_spec__0(lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedArg;
LEAN_EXPORT uint8_t l_Lean_IR_UnreachableBranches_Value_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_interpFnBody(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_addFunctionSummary(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_Value_addChoice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_UnreachableBranches_Value_beq___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at___Lean_IR_elimDeadBranches_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_findAtSorted_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_elimDeadAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_updateCurrFnSummary(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_UnreachableBranches_updateJPParamsAssignment_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_updateVarAssignment(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_mkPersistentArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___Lean_IR_UnreachableBranches_findVarValue_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_formatArray___at___Lean_IR_UnreachableBranches_Value_format_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_instToStringValue___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_initFn____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177_(lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_IR_elimDeadBranches_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_reprValue___lam__0____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_43_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_Value_truncate_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_UnreachableBranches_Value_truncate_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_initFn___lam__2____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_IR_UnreachableBranches_updateCurrFnSummary_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_UnreachableBranches_markJPVisited_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_UnreachableBranches_interpFnBody_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_reprValue____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_43__spec__0___redArg___lam__0(lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_UnreachableBranches_inferStep_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_markJPVisited_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_UnreachableBranches_inferStep_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_UnreachableBranches_markJPVisited_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_declLt___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_setBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___Lean_IR_UnreachableBranches_Value_beq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_updateBody_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_UnreachableBranches_inferStep_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_resetVarAssignment___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_resetVarAssignment(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_findVarValue___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_UnreachableBranches_elimDeadAux_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_markJPVisited___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_formatArray___at___Lean_IR_UnreachableBranches_Value_format_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at___Lean_IR_UnreachableBranches_Value_merge_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_initFn___lam__3____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_Value_merge(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_IR_UnreachableBranches_projValue_spec__0(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_resetParamAssignment(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_interpExpr___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_findAtSorted_x3f(lean_object*, lean_object*);
lean_object* l_Array_qsort_sort___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_Value_toFormat___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_interpExpr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_UnreachableBranches_inferStep_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_resetNestedJPParams_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_reprValue____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_43__spec__0(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___List_format___at___Lean_IR_UnreachableBranches_Value_format_spec__2_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_resetParamAssignment___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_inferMain(lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_UnreachableBranches_Value_toFormat___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at___Lean_IR_elimDeadBranches_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_getFunctionSummary_x3f(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_IR_instBEqVarId___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_elimDead___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_Value_truncate(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdx_x3f_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_UnreachableBranches_initFn___lam__1____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177_(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_IR_UnreachableBranches_projValue_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_UnreachableBranches_elimDeadAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_findVarValue(lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_UnreachableBranches_interpExpr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_IR_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_Value_beq___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_UnreachableBranches_interpExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_IR_UnreachableBranches_Value_merge_spec__1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_UnreachableBranches_containsCtor___lam__0(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_IR_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_UnreachableBranches_updateJPParamsAssignment_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_UnreachableBranches_inferStep_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_findArgValue(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_Value_beq___lam__2___boxed(lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_addJP(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_sortEntries(lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_IR_UnreachableBranches_getFunctionSummary_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_UnreachableBranches_interpFnBody_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_containsCtor___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_UnreachableBranches_inferStep_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_UnreachableBranches_markJPVisited_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_markJPVisited_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_markJPVisited_spec__1___redArg(lean_object*);
extern lean_object* l_Lean_Name_instBEq;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___Lean_IR_UnreachableBranches_findVarValue_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___Lean_IR_UnreachableBranches_updateCurrFnSummary_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_initFn___lam__0____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177_(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_updateJPParamsAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_IR_UnreachableBranches_updateCurrFnSummary_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_inferStep___boxed(lean_object*, lean_object*);
uint8_t l_List_any___redArg(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo___redArg____x40_Lean_Compiler_IR_Basic___hyg_1499_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_Value_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_Value_instToFormat;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_resetNestedJPParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_markJPVisited_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_IR_elimDeadBranches_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_instInhabitedList(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_UnreachableBranches_interpFnBody_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_elimDeadAux___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_getJPBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_IR_UnreachableBranches_getFunctionSummary_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_IR_UnreachableBranches_Value_truncate_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instHashableName;
lean_object* l_Std_HashSet_instInhabited(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_IR_UnreachableBranches_instInhabitedValue() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_reprValue____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_43__spec__0___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_reprValue____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_43_(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_reprValue____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_43__spec__0___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("[]", 2, 2);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_alloc_closure((void*)(l_List_repr___at_____private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_reprValue____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_43__spec__0___redArg___lam__0), 1, 0);
x_5 = lean_mk_string_unchecked("[", 1, 1);
x_6 = lean_mk_string_unchecked(",", 1, 1);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_box(1);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_inc(x_1);
x_10 = l_Std_Format_joinSep(lean_box(0), x_4, x_1, x_9);
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_12 = lean_ctor_get(x_1, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 0);
lean_dec(x_13);
x_14 = lean_mk_string_unchecked("]", 1, 1);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_to_int(x_15);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_10);
lean_ctor_set(x_1, 0, x_17);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_14);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_22, 0, x_20);
x_23 = lean_unbox(x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_23);
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_1);
x_24 = lean_mk_string_unchecked("]", 1, 1);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_to_int(x_25);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_5);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_10);
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_24);
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_33, 0, x_31);
x_34 = lean_unbox(x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_34);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_reprValue____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_43__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_repr___at_____private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_reprValue____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_43__spec__0___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_reprValue___lam__0____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_43_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_reprValue____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_43_(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_reprValue____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_43_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_12; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_unsigned_to_nat(1024u);
x_32 = lean_nat_dec_le(x_31, x_2);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_unsigned_to_nat(2u);
x_34 = lean_nat_to_int(x_33);
x_3 = x_34;
goto block_11;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_to_int(x_35);
x_3 = x_36;
goto block_11;
}
}
case 1:
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_unsigned_to_nat(1024u);
x_38 = lean_nat_dec_le(x_37, x_2);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_unsigned_to_nat(2u);
x_40 = lean_nat_to_int(x_39);
x_12 = x_40;
goto block_20;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_to_int(x_41);
x_12 = x_42;
goto block_20;
}
}
case 2:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_76; uint8_t x_77; 
x_43 = lean_ctor_get(x_1, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_1, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_45 = x_1;
} else {
 lean_dec_ref(x_1);
 x_45 = lean_box(0);
}
x_46 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_reprValue___lam__0____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_43_), 1, 0);
x_76 = lean_unsigned_to_nat(1024u);
x_77 = lean_nat_dec_le(x_76, x_2);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_unsigned_to_nat(2u);
x_79 = lean_nat_to_int(x_78);
x_47 = x_79;
goto block_75;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_nat_to_int(x_80);
x_47 = x_81;
goto block_75;
}
block_75:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_48 = lean_mk_string_unchecked("Lean.IR.UnreachableBranches.Value.ctor", 38, 38);
x_49 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_box(1);
if (lean_is_scalar(x_45)) {
 x_51 = lean_alloc_ctor(5, 2, 0);
} else {
 x_51 = x_45;
 lean_ctor_set_tag(x_51, 5);
}
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo___redArg____x40_Lean_Compiler_IR_Basic___hyg_1499_(x_43);
x_53 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_50);
x_55 = lean_array_get_size(x_44);
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_nat_dec_eq(x_55, x_56);
lean_dec(x_55);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_58 = lean_mk_string_unchecked("#[", 2, 2);
x_59 = lean_array_to_list(x_44);
x_60 = lean_mk_string_unchecked(",", 1, 1);
x_61 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_50);
x_63 = l_Std_Format_joinSep(lean_box(0), x_46, x_59, x_62);
x_64 = lean_mk_string_unchecked("]", 1, 1);
x_65 = lean_unsigned_to_nat(2u);
x_66 = lean_nat_to_int(x_65);
x_67 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_67, 0, x_58);
x_68 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_63);
x_69 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_69, 0, x_64);
x_70 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_71, 0, x_66);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Std_Format_fill(x_71);
x_21 = x_47;
x_22 = x_54;
x_23 = x_72;
goto block_30;
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_46);
lean_dec(x_44);
x_73 = lean_mk_string_unchecked("#[]", 3, 3);
x_74 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_21 = x_47;
x_22 = x_54;
x_23 = x_74;
goto block_30;
}
}
}
default: 
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_97; uint8_t x_98; 
x_82 = lean_ctor_get(x_1, 0);
lean_inc(x_82);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_83 = x_1;
} else {
 lean_dec_ref(x_1);
 x_83 = lean_box(0);
}
x_97 = lean_unsigned_to_nat(1024u);
x_98 = lean_nat_dec_le(x_97, x_2);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_unsigned_to_nat(2u);
x_100 = lean_nat_to_int(x_99);
x_84 = x_100;
goto block_96;
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_unsigned_to_nat(1u);
x_102 = lean_nat_to_int(x_101);
x_84 = x_102;
goto block_96;
}
block_96:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; 
x_85 = lean_mk_string_unchecked("Lean.IR.UnreachableBranches.Value.choice", 40, 40);
if (lean_is_scalar(x_83)) {
 x_86 = lean_alloc_ctor(3, 1, 0);
} else {
 x_86 = x_83;
}
lean_ctor_set(x_86, 0, x_85);
x_87 = lean_box(1);
x_88 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_List_repr___at_____private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_reprValue____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_43__spec__0___redArg(x_82);
x_90 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_91, 0, x_84);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_box(0);
x_93 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_93, 0, x_91);
x_94 = lean_unbox(x_92);
lean_ctor_set_uint8(x_93, sizeof(void*)*1, x_94);
x_95 = l_Repr_addAppParen(x_93, x_2);
return x_95;
}
}
}
block_11:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_4 = lean_mk_string_unchecked("Lean.IR.UnreachableBranches.Value.bot", 37, 37);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_9);
x_10 = l_Repr_addAppParen(x_8, x_2);
return x_10;
}
block_20:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_13 = lean_mk_string_unchecked("Lean.IR.UnreachableBranches.Value.top", 37, 37);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_17, 0, x_15);
x_18 = lean_unbox(x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_18);
x_19 = l_Repr_addAppParen(x_17, x_2);
return x_19;
}
block_30:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_27, 0, x_25);
x_28 = lean_unbox(x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_28);
x_29 = l_Repr_addAppParen(x_27, x_2);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_reprValue____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_43__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_repr___at_____private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_reprValue____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_43__spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_reprValue____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_43____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_reprValue____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_43_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_UnreachableBranches_instReprValue() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_reprValue____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_43____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_IR_UnreachableBranches_Value_toFormat_spec__0(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_mk_string_unchecked(" ", 1, 1);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_IR_UnreachableBranches_Value_toFormat(x_5);
x_10 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_10);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = lean_mk_string_unchecked(" ", 1, 1);
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_IR_UnreachableBranches_Value_toFormat(x_12);
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_2);
x_1 = x_13;
x_2 = x_18;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_IR_UnreachableBranches_Value_toFormat_spec__1(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_IR_UnreachableBranches_Value_toFormat(x_5);
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
x_11 = l_Lean_IR_UnreachableBranches_Value_toFormat(x_9);
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
LEAN_EXPORT uint8_t l_Lean_IR_UnreachableBranches_Value_toFormat___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_UnreachableBranches_Value_toFormat___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_Value_toFormat(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("⊥", 3, 1);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
case 1:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_mk_string_unchecked("⊤", 3, 1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
case 2:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = l_Array_isEmpty___redArg(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_10 = lean_box(x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_Value_toFormat___lam__0___boxed), 2, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_box(1);
x_14 = lean_unbox(x_13);
x_15 = l_Lean_Name_toString(x_12, x_14, x_11);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_array_to_list(x_8);
x_18 = lean_box(0);
x_19 = l_List_mapTR_loop___at___Lean_IR_UnreachableBranches_Value_toFormat_spec__0(x_17, x_18);
x_20 = l_Std_Format_join(x_19);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_20);
lean_ctor_set(x_1, 0, x_16);
x_21 = lean_mk_string_unchecked("(", 1, 1);
x_22 = lean_mk_string_unchecked(")", 1, 1);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_to_int(x_23);
x_25 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_25, 0, x_21);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_1);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_22);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_31, 0, x_29);
x_32 = lean_unbox(x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_32);
return x_31;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_free_object(x_1);
lean_dec(x_8);
x_33 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_Value_toFormat___lam__1___boxed), 1, 0);
x_34 = lean_ctor_get(x_7, 0);
lean_inc(x_34);
lean_dec(x_7);
x_35 = l_Lean_Name_toString(x_34, x_9, x_33);
x_36 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_1);
x_39 = l_Array_isEmpty___redArg(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_40 = lean_box(x_39);
x_41 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_Value_toFormat___lam__0___boxed), 2, 1);
lean_closure_set(x_41, 0, x_40);
x_42 = lean_ctor_get(x_37, 0);
lean_inc(x_42);
lean_dec(x_37);
x_43 = lean_box(1);
x_44 = lean_unbox(x_43);
x_45 = l_Lean_Name_toString(x_42, x_44, x_41);
x_46 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_array_to_list(x_38);
x_48 = lean_box(0);
x_49 = l_List_mapTR_loop___at___Lean_IR_UnreachableBranches_Value_toFormat_spec__0(x_47, x_48);
x_50 = l_Std_Format_join(x_49);
x_51 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_51, 0, x_46);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_mk_string_unchecked("(", 1, 1);
x_53 = lean_mk_string_unchecked(")", 1, 1);
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_to_int(x_54);
x_56 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_56, 0, x_52);
x_57 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_51);
x_58 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_58, 0, x_53);
x_59 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_62, 0, x_60);
x_63 = lean_unbox(x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_63);
return x_62;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_38);
x_64 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_Value_toFormat___lam__1___boxed), 1, 0);
x_65 = lean_ctor_get(x_37, 0);
lean_inc(x_65);
lean_dec(x_37);
x_66 = l_Lean_Name_toString(x_65, x_39, x_64);
x_67 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
}
default: 
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_1);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_69 = lean_ctor_get(x_1, 0);
x_70 = lean_box(0);
x_71 = l_List_mapTR_loop___at___Lean_IR_UnreachableBranches_Value_toFormat_spec__1(x_69, x_70);
x_72 = lean_mk_string_unchecked(" | ", 3, 3);
lean_ctor_set(x_1, 0, x_72);
x_73 = l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(x_71, x_1);
x_74 = lean_mk_string_unchecked("(", 1, 1);
x_75 = lean_mk_string_unchecked(")", 1, 1);
x_76 = lean_unsigned_to_nat(1u);
x_77 = lean_nat_to_int(x_76);
x_78 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_78, 0, x_74);
x_79 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_73);
x_80 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_80, 0, x_75);
x_81 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_82, 0, x_77);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_84, 0, x_82);
x_85 = lean_unbox(x_83);
lean_ctor_set_uint8(x_84, sizeof(void*)*1, x_85);
return x_84;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_86 = lean_ctor_get(x_1, 0);
lean_inc(x_86);
lean_dec(x_1);
x_87 = lean_box(0);
x_88 = l_List_mapTR_loop___at___Lean_IR_UnreachableBranches_Value_toFormat_spec__1(x_86, x_87);
x_89 = lean_mk_string_unchecked(" | ", 3, 3);
x_90 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_91 = l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(x_88, x_90);
x_92 = lean_mk_string_unchecked("(", 1, 1);
x_93 = lean_mk_string_unchecked(")", 1, 1);
x_94 = lean_unsigned_to_nat(1u);
x_95 = lean_nat_to_int(x_94);
x_96 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_96, 0, x_92);
x_97 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_91);
x_98 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_98, 0, x_93);
x_99 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_100, 0, x_95);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_box(0);
x_102 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_102, 0, x_100);
x_103 = lean_unbox(x_101);
lean_ctor_set_uint8(x_102, sizeof(void*)*1, x_103);
return x_102;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_Value_toFormat___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_IR_UnreachableBranches_Value_toFormat___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_Value_toFormat___lam__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_UnreachableBranches_Value_toFormat___lam__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_UnreachableBranches_instToFormatValue() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_Value_toFormat), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_instToStringValue___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_IR_UnreachableBranches_Value_toFormat(x_1);
x_3 = lean_unsigned_to_nat(120u);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_format_pretty(x_2, x_3, x_4, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_UnreachableBranches_instToStringValue() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_instToStringValue___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___Lean_IR_UnreachableBranches_Value_beq_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 1)
{
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_8 = lean_array_fget(x_1, x_7);
x_9 = lean_array_fget(x_2, x_7);
x_10 = l_Lean_IR_UnreachableBranches_Value_beq(x_8, x_9);
if (x_10 == 0)
{
lean_dec(x_7);
return x_10;
}
else
{
x_3 = x_7;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___Lean_IR_UnreachableBranches_Value_beq_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Array_isEqvAux___at___Lean_IR_UnreachableBranches_Value_beq_spec__0___redArg(x_1, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_UnreachableBranches_Value_beq___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_IR_UnreachableBranches_Value_beq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_UnreachableBranches_Value_beq___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_Value_beq___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_List_any___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_UnreachableBranches_Value_beq___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_IR_UnreachableBranches_Value_beq(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_UnreachableBranches_Value_beq___lam__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_Value_beq___lam__2___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_List_any___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_UnreachableBranches_Value_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
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
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(1);
x_8 = lean_unbox(x_7);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
return x_10;
}
}
case 2:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_Lean_IR_CtorInfo_beq(x_11, x_13);
lean_dec(x_13);
lean_dec(x_11);
if (x_15 == 0)
{
lean_dec(x_14);
lean_dec(x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_array_get_size(x_12);
x_17 = lean_array_get_size(x_14);
x_18 = lean_nat_dec_eq(x_16, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = l_Array_isEqvAux___at___Lean_IR_UnreachableBranches_Value_beq_spec__0___redArg(x_12, x_14, x_16);
lean_dec(x_14);
lean_dec(x_12);
return x_19;
}
}
}
else
{
lean_object* x_20; uint8_t x_21; 
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = lean_unbox(x_20);
return x_21;
}
}
default: 
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
lean_dec(x_2);
lean_inc(x_23);
x_24 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_Value_beq___lam__1___boxed), 2, 1);
lean_closure_set(x_24, 0, x_23);
lean_inc(x_22);
x_25 = l_List_all___redArg(x_22, x_24);
if (x_25 == 0)
{
lean_dec(x_23);
lean_dec(x_22);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_Value_beq___lam__3___boxed), 2, 1);
lean_closure_set(x_26, 0, x_22);
x_27 = l_List_all___redArg(x_23, x_26);
return x_27;
}
}
else
{
lean_object* x_28; uint8_t x_29; 
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_box(0);
x_29 = lean_unbox(x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___Lean_IR_UnreachableBranches_Value_beq_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_isEqvAux___at___Lean_IR_UnreachableBranches_Value_beq_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___Lean_IR_UnreachableBranches_Value_beq_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_isEqvAux___at___Lean_IR_UnreachableBranches_Value_beq_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_Value_beq___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_UnreachableBranches_Value_beq___lam__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_Value_beq___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_UnreachableBranches_Value_beq___lam__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_Value_beq___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_UnreachableBranches_Value_beq___lam__2(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_Value_beq___lam__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_UnreachableBranches_Value_beq___lam__3(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_Value_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_UnreachableBranches_Value_beq(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_UnreachableBranches_Value_instBEq() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_Value_beq___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_UnreachableBranches_Value_addChoice_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_instInhabitedList(lean_box(0));
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_Value_addChoice(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; 
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_2);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 2)
{
if (lean_obj_tag(x_3) == 2)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_2, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
x_19 = l_Lean_IR_CtorInfo_beq(x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = l_Lean_IR_UnreachableBranches_Value_addChoice(x_1, x_15, x_3);
lean_ctor_set(x_2, 1, x_20);
return x_2;
}
else
{
lean_object* x_21; 
x_21 = lean_apply_2(x_1, x_13, x_3);
lean_ctor_set(x_2, 0, x_21);
return x_2;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_3, 0);
lean_inc(x_24);
x_25 = l_Lean_IR_CtorInfo_beq(x_23, x_24);
lean_dec(x_24);
lean_dec(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Lean_IR_UnreachableBranches_Value_addChoice(x_1, x_22, x_3);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_13);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_apply_2(x_1, x_13, x_3);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_22);
return x_29;
}
}
}
else
{
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_11;
}
}
else
{
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_11;
}
}
block_11:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_mk_string_unchecked("Lean.Compiler.IR.ElimDeadBranches", 33, 33);
x_5 = lean_mk_string_unchecked("Lean.IR.UnreachableBranches.Value.addChoice", 43, 43);
x_6 = lean_unsigned_to_nat(57u);
x_7 = lean_unsigned_to_nat(12u);
x_8 = lean_mk_string_unchecked("invalid addChoice", 17, 17);
x_9 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_10 = l_panic___at___Lean_IR_UnreachableBranches_Value_addChoice_spec__0(x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at___Lean_IR_UnreachableBranches_Value_merge_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 1)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_4, x_8);
x_10 = lean_nat_sub(x_3, x_4);
lean_dec(x_4);
x_11 = lean_array_fget(x_1, x_10);
x_12 = lean_box(0);
x_13 = lean_array_get(x_12, x_2, x_10);
lean_dec(x_10);
x_14 = l_Lean_IR_UnreachableBranches_Value_merge(x_11, x_13);
x_15 = lean_array_push(x_5, x_14);
x_4 = x_9;
x_5 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at___Lean_IR_UnreachableBranches_Value_merge_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_foldTR_loop___at___Lean_IR_UnreachableBranches_Value_merge_spec__0___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_IR_UnreachableBranches_Value_merge_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_Value_merge), 2, 0);
x_6 = l_Lean_IR_UnreachableBranches_Value_addChoice(x_5, x_1, x_3);
x_1 = x_6;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_Value_merge(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
return x_2;
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
return x_2;
}
else
{
lean_dec(x_2);
return x_1;
}
}
case 2:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
return x_1;
}
case 1:
{
lean_dec(x_1);
return x_2;
}
case 2:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = l_Lean_IR_CtorInfo_beq(x_3, x_5);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_2, 1);
lean_dec(x_13);
x_14 = lean_ctor_get(x_2, 0);
lean_dec(x_14);
x_15 = lean_array_get_size(x_4);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_mk_empty_array_with_capacity(x_16);
lean_inc(x_15);
x_18 = l_Nat_foldTR_loop___at___Lean_IR_UnreachableBranches_Value_merge_spec__0___redArg(x_4, x_6, x_15, x_15, x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_18);
lean_ctor_set(x_2, 0, x_3);
return x_2;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_2);
x_19 = lean_array_get_size(x_4);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_mk_empty_array_with_capacity(x_20);
lean_inc(x_19);
x_22 = l_Nat_foldTR_loop___at___Lean_IR_UnreachableBranches_Value_merge_spec__0___redArg(x_4, x_6, x_19, x_19, x_21);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_4);
x_23 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
default: 
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_2);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_Value_merge), 2, 0);
x_27 = l_Lean_IR_UnreachableBranches_Value_addChoice(x_26, x_25, x_1);
lean_ctor_set(x_2, 0, x_27);
return x_2;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
lean_dec(x_2);
x_29 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_Value_merge), 2, 0);
x_30 = l_Lean_IR_UnreachableBranches_Value_addChoice(x_29, x_28, x_1);
x_31 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
}
default: 
{
switch (lean_obj_tag(x_2)) {
case 0:
{
return x_1;
}
case 1:
{
lean_dec(x_1);
return x_2;
}
case 2:
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_1);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_1, 0);
x_34 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_Value_merge), 2, 0);
x_35 = l_Lean_IR_UnreachableBranches_Value_addChoice(x_34, x_33, x_2);
lean_ctor_set(x_1, 0, x_35);
return x_1;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
lean_dec(x_1);
x_37 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_Value_merge), 2, 0);
x_38 = l_Lean_IR_UnreachableBranches_Value_addChoice(x_37, x_36, x_2);
x_39 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
default: 
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_2);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_2, 0);
x_43 = l_List_foldl___at___Lean_IR_UnreachableBranches_Value_merge_spec__1(x_42, x_40);
lean_ctor_set(x_2, 0, x_43);
return x_2;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_2, 0);
lean_inc(x_44);
lean_dec(x_2);
x_45 = l_List_foldl___at___Lean_IR_UnreachableBranches_Value_merge_spec__1(x_44, x_40);
x_46 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at___Lean_IR_UnreachableBranches_Value_merge_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_foldTR_loop___at___Lean_IR_UnreachableBranches_Value_merge_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at___Lean_IR_UnreachableBranches_Value_merge_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_foldTR_loop___at___Lean_IR_UnreachableBranches_Value_merge_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_formatArray___at___Lean_IR_UnreachableBranches_Value_format_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_mk_string_unchecked(" ", 1, 1);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_IR_UnreachableBranches_Value_format(x_6);
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
x_4 = x_11;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatArray___at___Lean_IR_UnreachableBranches_Value_format_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_box(0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_usize_of_nat(x_3);
x_8 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_IR_formatArray___at___Lean_IR_UnreachableBranches_Value_format_spec__0_spec__0(x_1, x_7, x_8, x_2);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Std_Format_joinSep___at___List_format___at___Lean_IR_UnreachableBranches_Value_format_spec__2_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 0, x_2);
x_7 = l_Lean_IR_UnreachableBranches_Value_format(x_5);
x_8 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_7);
x_2 = x_8;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
lean_inc(x_1);
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_1);
x_13 = l_Lean_IR_UnreachableBranches_Value_format(x_10);
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_2 = x_14;
x_3 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___List_format___at___Lean_IR_UnreachableBranches_Value_format_spec__2_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_IR_UnreachableBranches_Value_format(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_IR_UnreachableBranches_Value_format(x_7);
x_9 = l_List_foldl___at___Std_Format_joinSep___at___List_format___at___Lean_IR_UnreachableBranches_Value_format_spec__2_spec__2_spec__2(x_2, x_8, x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_List_format___at___Lean_IR_UnreachableBranches_Value_format_spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("[]", 2, 2);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked(",", 1, 1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
lean_inc(x_1);
x_8 = l_Std_Format_joinSep___at___List_format___at___Lean_IR_UnreachableBranches_Value_format_spec__2_spec__2(x_1, x_7);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_mk_string_unchecked("[", 1, 1);
x_13 = lean_mk_string_unchecked("]", 1, 1);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_to_int(x_14);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_16);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_13);
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_21, 0, x_19);
x_22 = lean_unbox(x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_22);
return x_21;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_1);
x_23 = lean_mk_string_unchecked("[", 1, 1);
x_24 = lean_mk_string_unchecked("]", 1, 1);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_to_int(x_25);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_23);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_24);
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_33, 0, x_31);
x_34 = lean_unbox(x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_34);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_Value_format(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("bot", 3, 3);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
case 1:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_mk_string_unchecked("top", 3, 3);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
case 2:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_mk_string_unchecked("#", 1, 1);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Array_isEmpty___redArg(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_12 = lean_box(x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_Value_toFormat___lam__0___boxed), 2, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_box(1);
x_16 = lean_unbox(x_15);
x_17 = l_Lean_Name_toString(x_14, x_16, x_13);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_IR_formatArray___at___Lean_IR_UnreachableBranches_Value_format_spec__0(x_8);
lean_dec(x_8);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_19);
lean_ctor_set(x_1, 0, x_18);
x_20 = lean_mk_string_unchecked("(", 1, 1);
x_21 = lean_mk_string_unchecked(")", 1, 1);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_to_int(x_22);
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_20);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_1);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_21);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_30, 0, x_28);
x_31 = lean_unbox(x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_31);
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_10);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_8);
x_33 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_Value_toFormat___lam__1___boxed), 1, 0);
x_34 = lean_ctor_get(x_7, 0);
lean_inc(x_34);
lean_dec(x_7);
x_35 = l_Lean_Name_toString(x_34, x_11, x_33);
x_36 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_36);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_1);
x_39 = lean_mk_string_unchecked("#", 1, 1);
x_40 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = l_Array_isEmpty___redArg(x_38);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; 
x_42 = lean_box(x_41);
x_43 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_Value_toFormat___lam__0___boxed), 2, 1);
lean_closure_set(x_43, 0, x_42);
x_44 = lean_ctor_get(x_37, 0);
lean_inc(x_44);
lean_dec(x_37);
x_45 = lean_box(1);
x_46 = lean_unbox(x_45);
x_47 = l_Lean_Name_toString(x_44, x_46, x_43);
x_48 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = l_Lean_IR_formatArray___at___Lean_IR_UnreachableBranches_Value_format_spec__0(x_38);
lean_dec(x_38);
x_50 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_mk_string_unchecked("(", 1, 1);
x_52 = lean_mk_string_unchecked(")", 1, 1);
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_to_int(x_53);
x_55 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_55, 0, x_51);
x_56 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_50);
x_57 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_57, 0, x_52);
x_58 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_61, 0, x_59);
x_62 = lean_unbox(x_60);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_62);
x_63 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_63, 0, x_40);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_38);
x_64 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_Value_toFormat___lam__1___boxed), 1, 0);
x_65 = lean_ctor_get(x_37, 0);
lean_inc(x_65);
lean_dec(x_37);
x_66 = l_Lean_Name_toString(x_65, x_41, x_64);
x_67 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_68 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_68, 0, x_40);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
default: 
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_1);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_1, 0);
x_71 = lean_mk_string_unchecked("@", 1, 1);
lean_ctor_set(x_1, 0, x_71);
x_72 = l_List_format___at___Lean_IR_UnreachableBranches_Value_format_spec__2(x_70);
x_73 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_73, 0, x_1);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_1, 0);
lean_inc(x_74);
lean_dec(x_1);
x_75 = lean_mk_string_unchecked("@", 1, 1);
x_76 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_77 = l_List_format___at___Lean_IR_UnreachableBranches_Value_format_spec__2(x_74);
x_78 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_formatArray___at___Lean_IR_UnreachableBranches_Value_format_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_IR_formatArray___at___Lean_IR_UnreachableBranches_Value_format_spec__0_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatArray___at___Lean_IR_UnreachableBranches_Value_format_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_formatArray___at___Lean_IR_UnreachableBranches_Value_format_spec__0(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_UnreachableBranches_Value_instToFormat() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_Value_format), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_Value_instToString___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(120u);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_format_pretty(x_1, x_2, x_3, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_UnreachableBranches_Value_instToString() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_Value_instToString___lam__0), 1, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_Value_format), 1, 0);
x_3 = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, lean_box(0));
lean_closure_set(x_3, 2, lean_box(0));
lean_closure_set(x_3, 3, x_1);
lean_closure_set(x_3, 4, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_UnreachableBranches_Value_truncateMaxDepth() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(8u);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_UnreachableBranches_Value_truncate_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_5, x_4);
if (x_7 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_8 = lean_array_uget(x_6, x_5);
x_9 = lean_box(0);
x_10 = lean_array_uset(x_6, x_5, x_9);
lean_inc(x_2);
lean_inc(x_1);
x_11 = l_Lean_IR_UnreachableBranches_Value_truncate_go(x_1, x_8, x_2, x_3);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_5, x_13);
x_15 = lean_array_uset(x_10, x_5, x_11);
x_5 = x_14;
x_6 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_IR_UnreachableBranches_Value_truncate_go_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = l_List_reverse___redArg(x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Lean_IR_UnreachableBranches_Value_truncate_go(x_1, x_8, x_2, x_3);
lean_ctor_set(x_4, 1, x_5);
lean_ctor_set(x_4, 0, x_10);
{
lean_object* _tmp_3 = x_9;
lean_object* _tmp_4 = x_4;
x_4 = _tmp_3;
x_5 = _tmp_4;
}
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l_Lean_IR_UnreachableBranches_Value_truncate_go(x_1, x_12, x_2, x_3);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_5);
x_4 = x_13;
x_5 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_List_elem___at___Lean_IR_UnreachableBranches_Value_truncate_go_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
lean_dec(x_1);
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
lean_inc(x_1);
x_7 = l_Lean_IR_UnreachableBranches_Value_beq(x_1, x_5);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_dec(x_6);
lean_dec(x_1);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_Value_truncate_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 1)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(1);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_4, x_8);
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_12 = x_2;
} else {
 lean_dec_ref(x_2);
 x_12 = lean_box(0);
}
x_19 = lean_ctor_get(x_10, 0);
lean_inc(x_19);
x_20 = l_Lean_Name_getPrefix(x_19);
lean_dec(x_19);
x_21 = l_Lean_NameSet_contains(x_3, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_inc(x_20);
lean_inc(x_1);
x_22 = l_Lean_Environment_find_x3f(x_1, x_20, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_dec(x_20);
x_13 = x_3;
goto block_18;
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 5)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get_uint8(x_24, sizeof(void*)*6);
lean_dec(x_24);
if (x_25 == 0)
{
lean_dec(x_20);
x_13 = x_3;
goto block_18;
}
else
{
lean_object* x_26; 
x_26 = l_Lean_NameSet_insert(x_3, x_20);
x_13 = x_26;
goto block_18;
}
}
else
{
lean_dec(x_23);
lean_dec(x_20);
x_13 = x_3;
goto block_18;
}
}
}
else
{
lean_object* x_27; 
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_27 = lean_box(1);
return x_27;
}
block_18:
{
size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_array_size(x_11);
x_15 = lean_usize_of_nat(x_5);
x_16 = l_Array_mapMUnsafe_map___at___Lean_IR_UnreachableBranches_Value_truncate_go_spec__0(x_1, x_13, x_9, x_14, x_15, x_11);
lean_dec(x_9);
if (lean_is_scalar(x_12)) {
 x_17 = lean_alloc_ctor(2, 2, 0);
} else {
 x_17 = x_12;
}
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
case 3:
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_2);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_2, 0);
x_30 = lean_box(0);
x_31 = l_List_mapTR_loop___at___Lean_IR_UnreachableBranches_Value_truncate_go_spec__1(x_1, x_3, x_9, x_29, x_30);
lean_dec(x_9);
x_32 = lean_box(1);
lean_inc(x_31);
x_33 = l_List_elem___at___Lean_IR_UnreachableBranches_Value_truncate_go_spec__2(x_32, x_31);
if (x_33 == 0)
{
lean_ctor_set(x_2, 0, x_31);
return x_2;
}
else
{
lean_dec(x_31);
lean_free_object(x_2);
return x_32;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
lean_dec(x_2);
x_35 = lean_box(0);
x_36 = l_List_mapTR_loop___at___Lean_IR_UnreachableBranches_Value_truncate_go_spec__1(x_1, x_3, x_9, x_34, x_35);
lean_dec(x_9);
x_37 = lean_box(1);
lean_inc(x_36);
x_38 = l_List_elem___at___Lean_IR_UnreachableBranches_Value_truncate_go_spec__2(x_37, x_36);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_39, 0, x_36);
return x_39;
}
else
{
lean_dec(x_36);
return x_37;
}
}
}
default: 
{
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_UnreachableBranches_Value_truncate_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_mapMUnsafe_map___at___Lean_IR_UnreachableBranches_Value_truncate_go_spec__0(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_IR_UnreachableBranches_Value_truncate_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_mapTR_loop___at___Lean_IR_UnreachableBranches_Value_truncate_go_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_elem___at___Lean_IR_UnreachableBranches_Value_truncate_go_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at___Lean_IR_UnreachableBranches_Value_truncate_go_spec__2(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_Value_truncate_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_UnreachableBranches_Value_truncate_go(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_Value_truncate(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(8u);
x_5 = l_Lean_IR_UnreachableBranches_Value_truncate_go(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_Value_widening(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_IR_UnreachableBranches_Value_merge(x_2, x_3);
x_5 = lean_box(0);
x_6 = l_Lean_IR_UnreachableBranches_Value_truncate(x_1, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_declLt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_Name_quickLt(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_declLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_declLt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_sortEntries(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_declLt___boxed), 2, 0);
x_7 = lean_nat_sub(x_2, x_5);
lean_dec(x_2);
x_8 = lean_nat_dec_le(x_3, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_inc(x_7);
x_9 = l_Array_qsort_sort___redArg(x_6, x_1, x_7, x_7);
lean_dec(x_7);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = l_Array_qsort_sort___redArg(x_6, x_1, x_3, x_7);
lean_dec(x_7);
return x_10;
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_findAtSorted_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_2);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_4, x_7);
lean_dec(x_4);
x_9 = lean_nat_dec_le(x_3, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_2);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_declLt___boxed), 2, 0);
x_14 = lean_alloc_closure((void*)(l_id___boxed), 2, 1);
lean_closure_set(x_14, 0, lean_box(0));
x_15 = l_Array_binSearchAux___redArg(x_13, x_14, x_1, x_12, x_3, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_box(0);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_findAtSorted_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_findAtSorted_x3f(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Array_qsort_sort___at___Lean_IR_UnreachableBranches_initFn____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177__spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_Name_quickLt(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_IR_UnreachableBranches_initFn____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177__spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_5 = lean_alloc_closure((void*)(l_Array_qsort_sort___at___Lean_IR_UnreachableBranches_initFn____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177__spec__0___redArg___lam__0___boxed), 2, 0);
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
x_10 = l_Array_qsort_sort___at___Lean_IR_UnreachableBranches_initFn____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177__spec__0___redArg(x_8, x_2, x_7);
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
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_IR_UnreachableBranches_initFn____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_qsort_sort___at___Lean_IR_UnreachableBranches_initFn____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177__spec__0___redArg(x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_initFn___lam__0____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_array_mk(x_1);
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_11; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_11 = lean_nat_dec_le(x_4, x_7);
if (x_11 == 0)
{
lean_inc(x_7);
x_8 = x_7;
goto block_10;
}
else
{
x_8 = x_4;
goto block_10;
}
block_10:
{
lean_object* x_9; 
x_9 = l_Array_qsort_sort___at___Lean_IR_UnreachableBranches_initFn____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177__spec__0___redArg(x_2, x_8, x_7);
lean_dec(x_7);
return x_9;
}
}
else
{
lean_dec(x_3);
return x_2;
}
}
}
LEAN_EXPORT uint8_t l_Lean_IR_UnreachableBranches_initFn___lam__1____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0(lean_box(0), x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(1);
x_6 = lean_unbox(x_5);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_initFn___lam__2____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_initFn___lam__3____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0(lean_box(0), x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_initFn____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_initFn___lam__0____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177_), 1, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_initFn___lam__1____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177____boxed), 2, 0);
x_4 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_initFn___lam__2____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177____boxed), 1, 0);
x_5 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_initFn___lam__3____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177_), 2, 0);
x_6 = l_Lean_Name_instBEq;
x_7 = l_Lean_instHashableName;
x_8 = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), x_6, x_7);
x_9 = lean_mk_string_unchecked("Lean", 4, 4);
x_10 = lean_mk_string_unchecked("IR", 2, 2);
x_11 = lean_mk_string_unchecked("UnreachableBranches", 19, 19);
x_12 = lean_mk_string_unchecked("functionSummariesExt", 20, 20);
x_13 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_12);
x_14 = lean_box(0);
lean_inc(x_5);
x_15 = lean_alloc_closure((void*)(l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed), 7, 4);
lean_closure_set(x_15, 0, lean_box(0));
lean_closure_set(x_15, 1, lean_box(0));
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_5);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_box(1);
x_18 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_5);
lean_ctor_set(x_18, 2, x_4);
lean_ctor_set(x_18, 3, x_2);
lean_ctor_set(x_18, 4, x_16);
x_19 = lean_unbox(x_14);
lean_ctor_set_uint8(x_18, sizeof(void*)*5, x_19);
x_20 = lean_unbox(x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*5 + 1, x_20);
x_21 = l_Lean_registerSimplePersistentEnvExtension(lean_box(0), lean_box(0), x_8, x_18, x_1);
lean_dec(x_8);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_IR_UnreachableBranches_initFn____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177__spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_qsort_sort___at___Lean_IR_UnreachableBranches_initFn____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177__spec__0___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_IR_UnreachableBranches_initFn____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177__spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsort_sort___at___Lean_IR_UnreachableBranches_initFn____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177__spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_IR_UnreachableBranches_initFn____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_qsort_sort___at___Lean_IR_UnreachableBranches_initFn____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177__spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_initFn___lam__1____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_UnreachableBranches_initFn___lam__1____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177_(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_initFn___lam__2____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_UnreachableBranches_initFn___lam__2____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177_(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_addFunctionSummary(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lean_IR_UnreachableBranches_functionSummariesExt;
lean_inc(x_2);
x_5 = l_Lean_Environment_addExtraName(x_1, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
x_7 = l_Lean_PersistentEnvExtension_addEntry(lean_box(0), lean_box(0), lean_box(0), x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_IR_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_nat_add(x_3, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_shiftr(x_5, x_6);
lean_dec(x_5);
x_8 = lean_array_fget(x_1, x_7);
x_9 = l_Array_qsort_sort___at___Lean_IR_UnreachableBranches_initFn____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177__spec__0___redArg___lam__0(x_8, x_2);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_4);
x_10 = l_Array_qsort_sort___at___Lean_IR_UnreachableBranches_initFn____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177__spec__0___redArg___lam__0(x_2, x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_8);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
lean_dec(x_8);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_7, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_nat_sub(x_7, x_6);
lean_dec(x_7);
x_15 = lean_nat_dec_lt(x_14, x_3);
if (x_15 == 0)
{
x_4 = x_14;
goto _start;
}
else
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_3);
x_17 = lean_box(0);
return x_17;
}
}
else
{
lean_object* x_18; 
lean_dec(x_7);
lean_dec(x_3);
x_18 = lean_box(0);
return x_18;
}
}
}
else
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_8);
lean_dec(x_3);
x_19 = lean_nat_add(x_7, x_6);
lean_dec(x_7);
x_20 = lean_nat_dec_le(x_19, x_4);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_19);
lean_dec(x_4);
x_21 = lean_box(0);
return x_21;
}
else
{
x_3 = x_19;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_IR_UnreachableBranches_getFunctionSummary_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_binSearchAux___at___Lean_IR_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_getFunctionSummary_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_Name_instBEq;
x_4 = l_Lean_instHashableName;
x_5 = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), x_3, x_4);
x_6 = l_Lean_Environment_getModuleIdxFor_x3f(x_1, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_IR_UnreachableBranches_functionSummariesExt;
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
lean_dec(x_8);
x_10 = l_Lean_SimplePersistentEnvExtension_getState(lean_box(0), lean_box(0), x_5, x_7, x_1, x_9);
x_11 = l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0(lean_box(0), x_10, x_2);
lean_dec(x_2);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
lean_dec(x_6);
x_13 = l_instInhabitedList(lean_box(0));
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_5);
x_15 = l_Lean_IR_UnreachableBranches_functionSummariesExt;
x_16 = lean_box(0);
x_17 = lean_unbox(x_16);
x_18 = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(x_14, x_15, x_1, x_12, x_17);
lean_dec(x_12);
lean_dec(x_1);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_get_size(x_18);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_2);
x_22 = lean_box(0);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_sub(x_20, x_23);
lean_dec(x_20);
x_25 = lean_nat_dec_le(x_19, x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_2);
x_26 = lean_box(0);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Array_binSearchAux___at___Lean_IR_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(x_18, x_28, x_19, x_24);
lean_dec(x_28);
lean_dec(x_18);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_box(0);
return x_30;
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 0);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
lean_ctor_set(x_29, 0, x_33);
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
lean_dec(x_29);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_IR_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___at___Lean_IR_UnreachableBranches_getFunctionSummary_x3f_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_IR_UnreachableBranches_getFunctionSummary_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_binSearchAux___at___Lean_IR_UnreachableBranches_getFunctionSummary_x3f_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___Lean_IR_UnreachableBranches_findVarValue_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___Lean_IR_UnreachableBranches_findVarValue_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_getD___at___Lean_IR_UnreachableBranches_findVarValue_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_findVarValue(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = l_Lean_IR_instBEqVarId;
x_5 = lean_alloc_closure((void*)(l_Lean_IR_instHashableVarId___lam__0___boxed), 1, 0);
x_6 = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), x_4, x_5);
lean_dec(x_5);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_array_get(x_6, x_7, x_8);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint64_t x_15; lean_object* x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; lean_object* x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; size_t x_24; size_t x_25; lean_object* x_26; size_t x_27; size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_box(0);
x_14 = lean_array_get_size(x_11);
x_15 = lean_uint64_of_nat(x_1);
x_16 = lean_unsigned_to_nat(32u);
x_17 = lean_uint64_of_nat(x_16);
x_18 = lean_uint64_shift_right(x_15, x_17);
x_19 = lean_uint64_xor(x_15, x_18);
x_20 = lean_unsigned_to_nat(16u);
x_21 = lean_uint64_of_nat(x_20);
x_22 = lean_uint64_shift_right(x_19, x_21);
x_23 = lean_uint64_xor(x_19, x_22);
x_24 = lean_uint64_to_usize(x_23);
x_25 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_usize_of_nat(x_26);
x_28 = lean_usize_sub(x_25, x_27);
x_29 = lean_usize_land(x_24, x_28);
x_30 = lean_array_uget(x_11, x_29);
lean_dec(x_11);
x_31 = l_Std_DHashMap_Internal_AssocList_getD___at___Lean_IR_UnreachableBranches_findVarValue_spec__0___redArg(x_1, x_13, x_30);
lean_dec(x_30);
lean_ctor_set(x_9, 1, x_3);
lean_ctor_set(x_9, 0, x_31);
return x_9;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint64_t x_35; lean_object* x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; lean_object* x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; size_t x_44; size_t x_45; lean_object* x_46; size_t x_47; size_t x_48; size_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_32 = lean_ctor_get(x_9, 1);
lean_inc(x_32);
lean_dec(x_9);
x_33 = lean_box(0);
x_34 = lean_array_get_size(x_32);
x_35 = lean_uint64_of_nat(x_1);
x_36 = lean_unsigned_to_nat(32u);
x_37 = lean_uint64_of_nat(x_36);
x_38 = lean_uint64_shift_right(x_35, x_37);
x_39 = lean_uint64_xor(x_35, x_38);
x_40 = lean_unsigned_to_nat(16u);
x_41 = lean_uint64_of_nat(x_40);
x_42 = lean_uint64_shift_right(x_39, x_41);
x_43 = lean_uint64_xor(x_39, x_42);
x_44 = lean_uint64_to_usize(x_43);
x_45 = lean_usize_of_nat(x_34);
lean_dec(x_34);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_usize_of_nat(x_46);
x_48 = lean_usize_sub(x_45, x_47);
x_49 = lean_usize_land(x_44, x_48);
x_50 = lean_array_uget(x_32, x_49);
lean_dec(x_32);
x_51 = l_Std_DHashMap_Internal_AssocList_getD___at___Lean_IR_UnreachableBranches_findVarValue_spec__0___redArg(x_1, x_33, x_50);
lean_dec(x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_3);
return x_52;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___Lean_IR_UnreachableBranches_findVarValue_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_getD___at___Lean_IR_UnreachableBranches_findVarValue_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___Lean_IR_UnreachableBranches_findVarValue_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_getD___at___Lean_IR_UnreachableBranches_findVarValue_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_findVarValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_UnreachableBranches_findVarValue(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_findArgValue(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Lean_IR_UnreachableBranches_findVarValue(x_4, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_findArgValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_UnreachableBranches_findArgValue(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__1_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__1_spec__1_spec__1___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_shiftl(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__1_spec__1___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_nat_dec_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__4___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_nat_dec_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__4___redArg(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__4___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_updateVarAssignment(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_5 = l_Lean_IR_UnreachableBranches_findVarValue(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_8 = x_5;
} else {
 lean_dec_ref(x_5);
 x_8 = lean_box(0);
}
x_9 = lean_box(0);
x_16 = lean_ctor_get(x_7, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_array_get_size(x_16);
x_19 = lean_nat_dec_lt(x_17, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_10 = x_16;
goto block_15;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_array_fget(x_16, x_17);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_28; lean_object* x_29; uint64_t x_30; lean_object* x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; lean_object* x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; size_t x_39; size_t x_40; lean_object* x_41; size_t x_42; size_t x_43; size_t x_44; lean_object* x_45; uint8_t x_46; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_array_fset(x_16, x_17, x_9);
x_28 = l_Lean_IR_UnreachableBranches_Value_merge(x_2, x_6);
x_29 = lean_array_get_size(x_23);
x_30 = lean_uint64_of_nat(x_1);
x_31 = lean_unsigned_to_nat(32u);
x_32 = lean_uint64_of_nat(x_31);
x_33 = lean_uint64_shift_right(x_30, x_32);
x_34 = lean_uint64_xor(x_30, x_33);
x_35 = lean_unsigned_to_nat(16u);
x_36 = lean_uint64_of_nat(x_35);
x_37 = lean_uint64_shift_right(x_34, x_36);
x_38 = lean_uint64_xor(x_34, x_37);
x_39 = lean_uint64_to_usize(x_38);
x_40 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_usize_of_nat(x_41);
x_43 = lean_usize_sub(x_40, x_42);
x_44 = lean_usize_land(x_39, x_43);
x_45 = lean_array_uget(x_23, x_44);
x_46 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__0___redArg(x_1, x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_47 = lean_nat_add(x_22, x_41);
lean_dec(x_22);
x_48 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_28);
lean_ctor_set(x_48, 2, x_45);
x_49 = lean_array_uset(x_23, x_44, x_48);
x_50 = lean_unsigned_to_nat(2u);
x_51 = lean_nat_shiftl(x_47, x_50);
x_52 = lean_unsigned_to_nat(3u);
x_53 = lean_nat_div(x_51, x_52);
lean_dec(x_51);
x_54 = lean_array_get_size(x_49);
x_55 = lean_nat_dec_le(x_53, x_54);
lean_dec(x_54);
lean_dec(x_53);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__1___redArg(x_49);
lean_ctor_set(x_20, 1, x_56);
lean_ctor_set(x_20, 0, x_47);
x_25 = x_20;
goto block_27;
}
else
{
lean_ctor_set(x_20, 1, x_49);
lean_ctor_set(x_20, 0, x_47);
x_25 = x_20;
goto block_27;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_box(0);
x_58 = lean_array_uset(x_23, x_44, x_57);
x_59 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__4___redArg(x_1, x_28, x_45);
x_60 = lean_array_uset(x_58, x_44, x_59);
lean_ctor_set(x_20, 1, x_60);
x_25 = x_20;
goto block_27;
}
block_27:
{
lean_object* x_26; 
x_26 = lean_array_fset(x_24, x_17, x_25);
x_10 = x_26;
goto block_15;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_67; lean_object* x_68; uint64_t x_69; lean_object* x_70; uint64_t x_71; uint64_t x_72; uint64_t x_73; lean_object* x_74; uint64_t x_75; uint64_t x_76; uint64_t x_77; size_t x_78; size_t x_79; lean_object* x_80; size_t x_81; size_t x_82; size_t x_83; lean_object* x_84; uint8_t x_85; 
x_61 = lean_ctor_get(x_20, 0);
x_62 = lean_ctor_get(x_20, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_20);
x_63 = lean_array_fset(x_16, x_17, x_9);
x_67 = l_Lean_IR_UnreachableBranches_Value_merge(x_2, x_6);
x_68 = lean_array_get_size(x_62);
x_69 = lean_uint64_of_nat(x_1);
x_70 = lean_unsigned_to_nat(32u);
x_71 = lean_uint64_of_nat(x_70);
x_72 = lean_uint64_shift_right(x_69, x_71);
x_73 = lean_uint64_xor(x_69, x_72);
x_74 = lean_unsigned_to_nat(16u);
x_75 = lean_uint64_of_nat(x_74);
x_76 = lean_uint64_shift_right(x_73, x_75);
x_77 = lean_uint64_xor(x_73, x_76);
x_78 = lean_uint64_to_usize(x_77);
x_79 = lean_usize_of_nat(x_68);
lean_dec(x_68);
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_usize_of_nat(x_80);
x_82 = lean_usize_sub(x_79, x_81);
x_83 = lean_usize_land(x_78, x_82);
x_84 = lean_array_uget(x_62, x_83);
x_85 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__0___redArg(x_1, x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_86 = lean_nat_add(x_61, x_80);
lean_dec(x_61);
x_87 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_87, 0, x_1);
lean_ctor_set(x_87, 1, x_67);
lean_ctor_set(x_87, 2, x_84);
x_88 = lean_array_uset(x_62, x_83, x_87);
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
lean_object* x_95; lean_object* x_96; 
x_95 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__1___redArg(x_88);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_86);
lean_ctor_set(x_96, 1, x_95);
x_64 = x_96;
goto block_66;
}
else
{
lean_object* x_97; 
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_86);
lean_ctor_set(x_97, 1, x_88);
x_64 = x_97;
goto block_66;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_box(0);
x_99 = lean_array_uset(x_62, x_83, x_98);
x_100 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__4___redArg(x_1, x_67, x_84);
x_101 = lean_array_uset(x_99, x_83, x_100);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_61);
lean_ctor_set(x_102, 1, x_101);
x_64 = x_102;
goto block_66;
}
block_66:
{
lean_object* x_65; 
x_65 = lean_array_fset(x_63, x_17, x_64);
x_10 = x_65;
goto block_15;
}
}
}
block_15:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 2);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
if (lean_is_scalar(x_8)) {
 x_14 = lean_alloc_ctor(0, 2, 0);
} else {
 x_14 = x_8;
}
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_updateVarAssignment___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_UnreachableBranches_updateVarAssignment(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_resetVarAssignment(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_4 = lean_box(0);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_array_get_size(x_11);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_1);
x_5 = x_11;
goto block_10;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_fget(x_11, x_12);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_23; lean_object* x_24; uint64_t x_25; lean_object* x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; lean_object* x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; size_t x_34; size_t x_35; lean_object* x_36; size_t x_37; size_t x_38; size_t x_39; lean_object* x_40; uint8_t x_41; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_array_fset(x_11, x_12, x_4);
x_23 = lean_box(0);
x_24 = lean_array_get_size(x_18);
x_25 = lean_uint64_of_nat(x_1);
x_26 = lean_unsigned_to_nat(32u);
x_27 = lean_uint64_of_nat(x_26);
x_28 = lean_uint64_shift_right(x_25, x_27);
x_29 = lean_uint64_xor(x_25, x_28);
x_30 = lean_unsigned_to_nat(16u);
x_31 = lean_uint64_of_nat(x_30);
x_32 = lean_uint64_shift_right(x_29, x_31);
x_33 = lean_uint64_xor(x_29, x_32);
x_34 = lean_uint64_to_usize(x_33);
x_35 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_usize_of_nat(x_36);
x_38 = lean_usize_sub(x_35, x_37);
x_39 = lean_usize_land(x_34, x_38);
x_40 = lean_array_uget(x_18, x_39);
x_41 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__0___redArg(x_1, x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_42 = lean_nat_add(x_17, x_36);
lean_dec(x_17);
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_23);
lean_ctor_set(x_43, 2, x_40);
x_44 = lean_array_uset(x_18, x_39, x_43);
x_45 = lean_unsigned_to_nat(2u);
x_46 = lean_nat_shiftl(x_42, x_45);
x_47 = lean_unsigned_to_nat(3u);
x_48 = lean_nat_div(x_46, x_47);
lean_dec(x_46);
x_49 = lean_array_get_size(x_44);
x_50 = lean_nat_dec_le(x_48, x_49);
lean_dec(x_49);
lean_dec(x_48);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__1___redArg(x_44);
lean_ctor_set(x_15, 1, x_51);
lean_ctor_set(x_15, 0, x_42);
x_20 = x_15;
goto block_22;
}
else
{
lean_ctor_set(x_15, 1, x_44);
lean_ctor_set(x_15, 0, x_42);
x_20 = x_15;
goto block_22;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_box(0);
x_53 = lean_array_uset(x_18, x_39, x_52);
x_54 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__4___redArg(x_1, x_23, x_40);
x_55 = lean_array_uset(x_53, x_39, x_54);
lean_ctor_set(x_15, 1, x_55);
x_20 = x_15;
goto block_22;
}
block_22:
{
lean_object* x_21; 
x_21 = lean_array_fset(x_19, x_12, x_20);
x_5 = x_21;
goto block_10;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_62; lean_object* x_63; uint64_t x_64; lean_object* x_65; uint64_t x_66; uint64_t x_67; uint64_t x_68; lean_object* x_69; uint64_t x_70; uint64_t x_71; uint64_t x_72; size_t x_73; size_t x_74; lean_object* x_75; size_t x_76; size_t x_77; size_t x_78; lean_object* x_79; uint8_t x_80; 
x_56 = lean_ctor_get(x_15, 0);
x_57 = lean_ctor_get(x_15, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_15);
x_58 = lean_array_fset(x_11, x_12, x_4);
x_62 = lean_box(0);
x_63 = lean_array_get_size(x_57);
x_64 = lean_uint64_of_nat(x_1);
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
x_79 = lean_array_uget(x_57, x_78);
x_80 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__0___redArg(x_1, x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_81 = lean_nat_add(x_56, x_75);
lean_dec(x_56);
x_82 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_62);
lean_ctor_set(x_82, 2, x_79);
x_83 = lean_array_uset(x_57, x_78, x_82);
x_84 = lean_unsigned_to_nat(2u);
x_85 = lean_nat_shiftl(x_81, x_84);
x_86 = lean_unsigned_to_nat(3u);
x_87 = lean_nat_div(x_85, x_86);
lean_dec(x_85);
x_88 = lean_array_get_size(x_83);
x_89 = lean_nat_dec_le(x_87, x_88);
lean_dec(x_88);
lean_dec(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__1___redArg(x_83);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_81);
lean_ctor_set(x_91, 1, x_90);
x_59 = x_91;
goto block_61;
}
else
{
lean_object* x_92; 
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_81);
lean_ctor_set(x_92, 1, x_83);
x_59 = x_92;
goto block_61;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_box(0);
x_94 = lean_array_uset(x_57, x_78, x_93);
x_95 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__4___redArg(x_1, x_62, x_79);
x_96 = lean_array_uset(x_94, x_78, x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_56);
lean_ctor_set(x_97, 1, x_96);
x_59 = x_97;
goto block_61;
}
block_61:
{
lean_object* x_60; 
x_60 = lean_array_fset(x_58, x_12, x_59);
x_5 = x_60;
goto block_10;
}
}
}
block_10:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_resetVarAssignment___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_UnreachableBranches_resetVarAssignment(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_resetParamAssignment(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_IR_UnreachableBranches_resetVarAssignment(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_resetParamAssignment___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_UnreachableBranches_resetParamAssignment(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_IR_UnreachableBranches_projValue_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Lean_IR_UnreachableBranches_projValue(x_4, x_1);
x_7 = l_Lean_IR_UnreachableBranches_Value_merge(x_2, x_6);
x_2 = x_7;
x_3 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_projValue(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_array_fget(x_3, x_2);
return x_7;
}
}
case 3:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_box(0);
x_10 = l_List_foldl___at___Lean_IR_UnreachableBranches_projValue_spec__0(x_2, x_9, x_8);
return x_10;
}
default: 
{
lean_inc(x_1);
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_IR_UnreachableBranches_projValue_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_foldl___at___Lean_IR_UnreachableBranches_projValue_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_projValue___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_UnreachableBranches_projValue(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_UnreachableBranches_interpExpr_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_2, x_1);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_8 = lean_array_uget(x_3, x_2);
x_9 = l_Lean_IR_UnreachableBranches_findArgValue(x_8, x_4, x_5);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_2, x_15);
x_17 = lean_array_uset(x_13, x_2, x_10);
x_2 = x_16;
x_3 = x_17;
x_5 = x_11;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Lean_IR_UnreachableBranches_interpExpr___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_name_eq(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_interpExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; size_t x_6; lean_object* x_7; size_t x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_usize_of_nat(x_7);
x_9 = l_Array_mapMUnsafe_map___at___Lean_IR_UnreachableBranches_interpExpr_spec__0(x_6, x_8, x_5, x_2, x_3);
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_ctor_set_tag(x_1, 2);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_9, 0, x_1);
return x_9;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_9);
lean_ctor_set_tag(x_1, 2);
lean_ctor_set(x_1, 1, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; size_t x_17; lean_object* x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_1);
x_17 = lean_array_size(x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_usize_of_nat(x_18);
x_20 = l_Array_mapMUnsafe_map___at___Lean_IR_UnreachableBranches_interpExpr_spec__0(x_17, x_19, x_16, x_2, x_3);
lean_dec(x_2);
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
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_21);
if (lean_is_scalar(x_23)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_23;
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
case 3:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_dec(x_1);
x_28 = l_Lean_IR_UnreachableBranches_findVarValue(x_27, x_2, x_3);
lean_dec(x_2);
lean_dec(x_27);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = l_Lean_IR_UnreachableBranches_projValue(x_30, x_26);
lean_dec(x_26);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_28, 0);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_28);
x_34 = l_Lean_IR_UnreachableBranches_projValue(x_32, x_26);
lean_dec(x_26);
lean_dec(x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
case 6:
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_1);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_ctor_get(x_1, 1);
lean_dec(x_38);
x_39 = lean_ctor_get(x_2, 2);
lean_inc(x_39);
lean_inc(x_37);
x_40 = l_Lean_IR_UnreachableBranches_getFunctionSummary_x3f(x_39, x_37);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_interpExpr___lam__0___boxed), 2, 1);
lean_closure_set(x_41, 0, x_37);
x_42 = lean_ctor_get(x_2, 1);
lean_inc(x_42);
lean_dec(x_2);
x_43 = lean_unsigned_to_nat(0u);
x_44 = l_Array_findIdx_x3f_loop___redArg(x_41, x_42, x_43);
lean_dec(x_42);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_box(1);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_3);
lean_ctor_set(x_1, 0, x_45);
return x_1;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_box(0);
x_48 = lean_ctor_get(x_3, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_48, 2);
lean_inc(x_49);
x_50 = lean_nat_dec_lt(x_46, x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_dec(x_48);
lean_dec(x_46);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_51; 
x_51 = l_outOfBounds___redArg(x_47);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_3);
lean_ctor_set(x_1, 0, x_51);
return x_1;
}
else
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_40, 0);
lean_inc(x_52);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_3);
lean_ctor_set(x_1, 0, x_52);
return x_1;
}
}
else
{
lean_object* x_53; 
x_53 = l_Lean_PersistentArray_get_x21___redArg(x_47, x_48, x_46);
lean_dec(x_46);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_3);
lean_ctor_set(x_1, 0, x_53);
return x_1;
}
}
}
else
{
lean_object* x_54; 
lean_dec(x_37);
lean_dec(x_2);
x_54 = lean_ctor_get(x_40, 0);
lean_inc(x_54);
lean_dec(x_40);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_3);
lean_ctor_set(x_1, 0, x_54);
return x_1;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_1, 0);
lean_inc(x_55);
lean_dec(x_1);
x_56 = lean_ctor_get(x_2, 2);
lean_inc(x_56);
lean_inc(x_55);
x_57 = l_Lean_IR_UnreachableBranches_getFunctionSummary_x3f(x_56, x_55);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_interpExpr___lam__0___boxed), 2, 1);
lean_closure_set(x_58, 0, x_55);
x_59 = lean_ctor_get(x_2, 1);
lean_inc(x_59);
lean_dec(x_2);
x_60 = lean_unsigned_to_nat(0u);
x_61 = l_Array_findIdx_x3f_loop___redArg(x_58, x_59, x_60);
lean_dec(x_59);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_box(1);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_3);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_64 = lean_ctor_get(x_61, 0);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_box(0);
x_66 = lean_ctor_get(x_3, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_66, 2);
lean_inc(x_67);
x_68 = lean_nat_dec_lt(x_64, x_67);
lean_dec(x_67);
if (x_68 == 0)
{
lean_dec(x_66);
lean_dec(x_64);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = l_outOfBounds___redArg(x_65);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_3);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_57, 0);
lean_inc(x_71);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_3);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = l_Lean_PersistentArray_get_x21___redArg(x_65, x_66, x_64);
lean_dec(x_64);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_3);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_55);
lean_dec(x_2);
x_75 = lean_ctor_get(x_57, 0);
lean_inc(x_75);
lean_dec(x_57);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_3);
return x_76;
}
}
}
default: 
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_2);
lean_dec(x_1);
x_77 = lean_box(1);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_3);
return x_78;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_UnreachableBranches_interpExpr_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l_Array_mapMUnsafe_map___at___Lean_IR_UnreachableBranches_interpExpr_spec__0(x_6, x_7, x_3, x_4, x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_interpExpr___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_UnreachableBranches_interpExpr___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_UnreachableBranches_containsCtor___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_IR_UnreachableBranches_containsCtor(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_UnreachableBranches_containsCtor(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; uint8_t x_4; 
lean_dec(x_2);
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
case 1:
{
lean_object* x_5; uint8_t x_6; 
lean_dec(x_2);
x_5 = lean_box(1);
x_6 = lean_unbox(x_5);
return x_6;
}
case 2:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_IR_CtorInfo_beq(x_7, x_2);
lean_dec(x_2);
lean_dec(x_7);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_containsCtor___lam__0___boxed), 2, 1);
lean_closure_set(x_10, 0, x_2);
x_11 = l_List_any___redArg(x_9, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_containsCtor___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_UnreachableBranches_containsCtor___lam__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_containsCtor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_UnreachableBranches_containsCtor(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_IR_UnreachableBranches_updateCurrFnSummary_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; size_t x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_usize_shift_right(x_4, x_5);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_shift_left(x_9, x_5);
x_11 = lean_unsigned_to_nat(5u);
x_12 = lean_usize_to_nat(x_7);
x_13 = lean_array_get_size(x_6);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_3);
if (x_15 == 0)
{
lean_object* x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_3, 0);
lean_dec(x_16);
x_17 = lean_usize_sub(x_10, x_9);
x_18 = lean_usize_of_nat(x_11);
x_19 = lean_usize_land(x_4, x_17);
x_20 = lean_usize_sub(x_5, x_18);
x_21 = lean_array_fget(x_6, x_12);
x_22 = lean_box(0);
x_23 = lean_array_fset(x_6, x_12, x_22);
x_24 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_IR_UnreachableBranches_updateCurrFnSummary_spec__0_spec__0___redArg(x_1, x_2, x_21, x_19, x_20);
x_25 = lean_array_fset(x_23, x_12, x_24);
lean_dec(x_12);
lean_ctor_set(x_3, 0, x_25);
return x_3;
}
else
{
size_t x_26; size_t x_27; size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_3);
x_26 = lean_usize_sub(x_10, x_9);
x_27 = lean_usize_of_nat(x_11);
x_28 = lean_usize_land(x_4, x_26);
x_29 = lean_usize_sub(x_5, x_27);
x_30 = lean_array_fget(x_6, x_12);
x_31 = lean_box(0);
x_32 = lean_array_fset(x_6, x_12, x_31);
x_33 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_IR_UnreachableBranches_updateCurrFnSummary_spec__0_spec__0___redArg(x_1, x_2, x_30, x_28, x_29);
x_34 = lean_array_fset(x_32, x_12, x_33);
lean_dec(x_12);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_3, 0);
lean_inc(x_36);
x_37 = lean_usize_to_nat(x_4);
x_38 = lean_array_get_size(x_36);
x_39 = lean_nat_dec_lt(x_37, x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_3);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_3, 0);
lean_dec(x_41);
x_42 = lean_array_fget(x_36, x_37);
x_43 = lean_box(0);
x_44 = lean_array_fset(x_36, x_37, x_43);
x_45 = lean_ctor_get(x_1, 2);
lean_inc(x_45);
lean_dec(x_1);
x_46 = l_Lean_IR_UnreachableBranches_Value_widening(x_45, x_2, x_42);
x_47 = lean_array_fset(x_44, x_37, x_46);
lean_dec(x_37);
lean_ctor_set(x_3, 0, x_47);
return x_3;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_3);
x_48 = lean_array_fget(x_36, x_37);
x_49 = lean_box(0);
x_50 = lean_array_fset(x_36, x_37, x_49);
x_51 = lean_ctor_get(x_1, 2);
lean_inc(x_51);
lean_dec(x_1);
x_52 = l_Lean_IR_UnreachableBranches_Value_widening(x_51, x_2, x_48);
x_53 = lean_array_fset(x_50, x_37, x_52);
lean_dec(x_37);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_IR_UnreachableBranches_updateCurrFnSummary_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_IR_UnreachableBranches_updateCurrFnSummary_spec__0_spec__0___redArg(x_1, x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___Lean_IR_UnreachableBranches_updateCurrFnSummary_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 3);
lean_inc(x_6);
x_7 = lean_nat_dec_le(x_6, x_5);
if (x_7 == 0)
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_usize_of_nat(x_5);
x_10 = lean_ctor_get_usize(x_4, 4);
x_11 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_IR_UnreachableBranches_updateCurrFnSummary_spec__0_spec__0___redArg(x_1, x_2, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 2);
lean_inc(x_13);
lean_dec(x_4);
x_14 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set(x_14, 3, x_6);
lean_ctor_set_usize(x_14, 4, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
x_21 = lean_ctor_get(x_4, 1);
lean_inc(x_21);
x_22 = lean_nat_sub(x_5, x_6);
x_23 = lean_array_get_size(x_21);
x_24 = lean_nat_dec_lt(x_22, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_dec(x_22);
lean_dec(x_2);
lean_dec(x_1);
x_16 = x_21;
goto block_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_array_fget(x_21, x_22);
x_26 = lean_box(0);
x_27 = lean_array_fset(x_21, x_22, x_26);
x_28 = lean_ctor_get(x_1, 2);
lean_inc(x_28);
lean_dec(x_1);
x_29 = l_Lean_IR_UnreachableBranches_Value_widening(x_28, x_2, x_25);
x_30 = lean_array_fset(x_27, x_22, x_29);
lean_dec(x_22);
x_16 = x_30;
goto block_20;
}
block_20:
{
lean_object* x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_4, 2);
lean_inc(x_17);
x_18 = lean_ctor_get_usize(x_4, 4);
lean_dec(x_4);
x_19 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_17);
lean_ctor_set(x_19, 3, x_6);
lean_ctor_set_usize(x_19, 4, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_updateCurrFnSummary(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_box(0);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_box(0);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
x_9 = l_Lean_PersistentArray_modify___at___Lean_IR_UnreachableBranches_updateCurrFnSummary_spec__0(x_2, x_1, x_4, x_8, x_5);
lean_dec(x_5);
x_10 = lean_ctor_get(x_3, 2);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_IR_UnreachableBranches_updateCurrFnSummary_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_IR_UnreachableBranches_updateCurrFnSummary_spec__0_spec__0___redArg(x_1, x_2, x_3, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_IR_UnreachableBranches_updateCurrFnSummary_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_9 = l_Lean_PersistentArray_modifyAux___at___Lean_PersistentArray_modify___at___Lean_IR_UnreachableBranches_updateCurrFnSummary_spec__0_spec__0(x_1, x_2, x_3, x_4, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___Lean_IR_UnreachableBranches_updateCurrFnSummary_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentArray_modify___at___Lean_IR_UnreachableBranches_updateCurrFnSummary_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_UnreachableBranches_markJPVisited_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_UnreachableBranches_markJPVisited_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_UnreachableBranches_markJPVisited_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_markJPVisited_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_markJPVisited_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_markJPVisited_spec__1_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_markJPVisited_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_markJPVisited_spec__1_spec__1_spec__1___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_markJPVisited_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_markJPVisited_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_markJPVisited_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_shiftl(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_markJPVisited_spec__1_spec__1___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_markJPVisited_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_markJPVisited_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_markJPVisited(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_23; uint8_t x_24; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint64_t x_81; lean_object* x_82; uint64_t x_83; uint64_t x_84; uint64_t x_85; lean_object* x_86; uint64_t x_87; uint64_t x_88; uint64_t x_89; size_t x_90; size_t x_91; lean_object* x_92; size_t x_93; size_t x_94; size_t x_95; lean_object* x_96; uint8_t x_97; 
x_12 = lean_alloc_closure((void*)(l_Lean_IR_instBEqVarId___lam__0___boxed), 2, 0);
x_13 = lean_alloc_closure((void*)(l_Lean_IR_instHashableVarId___lam__0___boxed), 1, 0);
x_14 = l_Std_HashSet_instInhabited(lean_box(0), x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
x_15 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_3, 2);
lean_inc(x_23);
x_78 = lean_array_get(x_14, x_23, x_15);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_80 = lean_array_get_size(x_79);
x_81 = lean_uint64_of_nat(x_1);
x_82 = lean_unsigned_to_nat(32u);
x_83 = lean_uint64_of_nat(x_82);
x_84 = lean_uint64_shift_right(x_81, x_83);
x_85 = lean_uint64_xor(x_81, x_84);
x_86 = lean_unsigned_to_nat(16u);
x_87 = lean_uint64_of_nat(x_86);
x_88 = lean_uint64_shift_right(x_85, x_87);
x_89 = lean_uint64_xor(x_85, x_88);
x_90 = lean_uint64_to_usize(x_89);
x_91 = lean_usize_of_nat(x_80);
lean_dec(x_80);
x_92 = lean_unsigned_to_nat(1u);
x_93 = lean_usize_of_nat(x_92);
x_94 = lean_usize_sub(x_91, x_93);
x_95 = lean_usize_land(x_90, x_94);
x_96 = lean_array_uget(x_79, x_95);
lean_dec(x_79);
x_97 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_UnreachableBranches_markJPVisited_spec__0___redArg(x_1, x_96);
lean_dec(x_96);
if (x_97 == 0)
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_box(1);
x_99 = lean_unbox(x_98);
x_24 = x_99;
goto block_77;
}
else
{
lean_object* x_100; uint8_t x_101; 
x_100 = lean_box(0);
x_101 = lean_unbox(x_100);
x_24 = x_101;
goto block_77;
}
block_11:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_7);
x_9 = lean_box(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
block_22:
{
lean_object* x_21; 
x_21 = lean_array_fset(x_16, x_15, x_20);
x_4 = x_17;
x_5 = x_18;
x_6 = x_19;
x_7 = x_21;
goto block_11;
}
block_77:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_3, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_3, 1);
lean_inc(x_26);
lean_dec(x_3);
x_27 = lean_array_get_size(x_23);
x_28 = lean_nat_dec_lt(x_15, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_dec(x_1);
x_4 = x_26;
x_5 = x_25;
x_6 = x_24;
x_7 = x_23;
goto block_11;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint64_t x_35; lean_object* x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; lean_object* x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; size_t x_44; size_t x_45; lean_object* x_46; size_t x_47; size_t x_48; size_t x_49; lean_object* x_50; uint8_t x_51; 
x_29 = lean_array_fget(x_23, x_15);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
x_32 = lean_box(0);
x_33 = lean_array_fset(x_23, x_15, x_32);
x_34 = lean_array_get_size(x_31);
x_35 = lean_uint64_of_nat(x_1);
x_36 = lean_unsigned_to_nat(32u);
x_37 = lean_uint64_of_nat(x_36);
x_38 = lean_uint64_shift_right(x_35, x_37);
x_39 = lean_uint64_xor(x_35, x_38);
x_40 = lean_unsigned_to_nat(16u);
x_41 = lean_uint64_of_nat(x_40);
x_42 = lean_uint64_shift_right(x_39, x_41);
x_43 = lean_uint64_xor(x_39, x_42);
x_44 = lean_uint64_to_usize(x_43);
x_45 = lean_usize_of_nat(x_34);
lean_dec(x_34);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_usize_of_nat(x_46);
x_48 = lean_usize_sub(x_45, x_47);
x_49 = lean_usize_land(x_44, x_48);
x_50 = lean_array_uget(x_31, x_49);
x_51 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_UnreachableBranches_markJPVisited_spec__0___redArg(x_1, x_50);
if (x_51 == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_29);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_53 = lean_ctor_get(x_29, 1);
lean_dec(x_53);
x_54 = lean_ctor_get(x_29, 0);
lean_dec(x_54);
x_55 = lean_nat_add(x_30, x_46);
lean_dec(x_30);
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_32);
lean_ctor_set(x_56, 2, x_50);
x_57 = lean_array_uset(x_31, x_49, x_56);
x_58 = lean_unsigned_to_nat(2u);
x_59 = lean_nat_shiftl(x_55, x_58);
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
x_64 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_markJPVisited_spec__1___redArg(x_57);
lean_ctor_set(x_29, 1, x_64);
lean_ctor_set(x_29, 0, x_55);
x_16 = x_33;
x_17 = x_26;
x_18 = x_25;
x_19 = x_24;
x_20 = x_29;
goto block_22;
}
else
{
lean_ctor_set(x_29, 1, x_57);
lean_ctor_set(x_29, 0, x_55);
x_16 = x_33;
x_17 = x_26;
x_18 = x_25;
x_19 = x_24;
x_20 = x_29;
goto block_22;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
lean_dec(x_29);
x_65 = lean_nat_add(x_30, x_46);
lean_dec(x_30);
x_66 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_66, 0, x_1);
lean_ctor_set(x_66, 1, x_32);
lean_ctor_set(x_66, 2, x_50);
x_67 = lean_array_uset(x_31, x_49, x_66);
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
x_74 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_markJPVisited_spec__1___redArg(x_67);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_65);
lean_ctor_set(x_75, 1, x_74);
x_16 = x_33;
x_17 = x_26;
x_18 = x_25;
x_19 = x_24;
x_20 = x_75;
goto block_22;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_65);
lean_ctor_set(x_76, 1, x_67);
x_16 = x_33;
x_17 = x_26;
x_18 = x_25;
x_19 = x_24;
x_20 = x_76;
goto block_22;
}
}
}
else
{
lean_dec(x_50);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_1);
x_16 = x_33;
x_17 = x_26;
x_18 = x_25;
x_19 = x_24;
x_20 = x_29;
goto block_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_UnreachableBranches_markJPVisited_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_UnreachableBranches_markJPVisited_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_UnreachableBranches_markJPVisited_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_UnreachableBranches_markJPVisited_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_markJPVisited___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_UnreachableBranches_markJPVisited(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_UnreachableBranches_updateJPParamsAssignment_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_5, x_9);
if (x_10 == 1)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_11 = lean_box(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_5, x_13);
lean_dec(x_5);
x_15 = lean_nat_sub(x_4, x_14);
x_16 = lean_nat_sub(x_15, x_13);
lean_dec(x_15);
x_17 = lean_array_fget(x_1, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_IR_UnreachableBranches_findVarValue(x_18, x_7, x_8);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_IR_instInhabitedArg;
x_23 = lean_array_get(x_22, x_2, x_16);
lean_dec(x_16);
x_24 = l_Lean_IR_UnreachableBranches_findArgValue(x_23, x_7, x_21);
lean_dec(x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_20);
x_27 = l_Lean_IR_UnreachableBranches_Value_merge(x_20, x_25);
lean_inc(x_27);
x_28 = l_Lean_IR_UnreachableBranches_Value_beq(x_27, x_20);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_29 = lean_ctor_get(x_3, 0);
x_30 = lean_box(1);
x_38 = lean_ctor_get(x_26, 0);
lean_inc(x_38);
x_39 = lean_array_get_size(x_38);
x_40 = lean_nat_dec_lt(x_29, x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_dec(x_27);
lean_dec(x_18);
x_31 = x_38;
goto block_37;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_box(0);
x_42 = lean_array_fget(x_38, x_29);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_50; uint64_t x_51; lean_object* x_52; uint64_t x_53; uint64_t x_54; uint64_t x_55; lean_object* x_56; uint64_t x_57; uint64_t x_58; uint64_t x_59; size_t x_60; size_t x_61; size_t x_62; size_t x_63; size_t x_64; lean_object* x_65; uint8_t x_66; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
x_46 = lean_array_fset(x_38, x_29, x_41);
x_50 = lean_array_get_size(x_45);
x_51 = lean_uint64_of_nat(x_18);
x_52 = lean_unsigned_to_nat(32u);
x_53 = lean_uint64_of_nat(x_52);
x_54 = lean_uint64_shift_right(x_51, x_53);
x_55 = lean_uint64_xor(x_51, x_54);
x_56 = lean_unsigned_to_nat(16u);
x_57 = lean_uint64_of_nat(x_56);
x_58 = lean_uint64_shift_right(x_55, x_57);
x_59 = lean_uint64_xor(x_55, x_58);
x_60 = lean_uint64_to_usize(x_59);
x_61 = lean_usize_of_nat(x_50);
lean_dec(x_50);
x_62 = lean_usize_of_nat(x_13);
x_63 = lean_usize_sub(x_61, x_62);
x_64 = lean_usize_land(x_60, x_63);
x_65 = lean_array_uget(x_45, x_64);
x_66 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__0___redArg(x_18, x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_67 = lean_nat_add(x_44, x_13);
lean_dec(x_44);
x_68 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_68, 0, x_18);
lean_ctor_set(x_68, 1, x_27);
lean_ctor_set(x_68, 2, x_65);
x_69 = lean_array_uset(x_45, x_64, x_68);
x_70 = lean_unsigned_to_nat(2u);
x_71 = lean_nat_shiftl(x_67, x_70);
x_72 = lean_unsigned_to_nat(3u);
x_73 = lean_nat_div(x_71, x_72);
lean_dec(x_71);
x_74 = lean_array_get_size(x_69);
x_75 = lean_nat_dec_le(x_73, x_74);
lean_dec(x_74);
lean_dec(x_73);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__1___redArg(x_69);
lean_ctor_set(x_42, 1, x_76);
lean_ctor_set(x_42, 0, x_67);
x_47 = x_42;
goto block_49;
}
else
{
lean_ctor_set(x_42, 1, x_69);
lean_ctor_set(x_42, 0, x_67);
x_47 = x_42;
goto block_49;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_box(0);
x_78 = lean_array_uset(x_45, x_64, x_77);
x_79 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__4___redArg(x_18, x_27, x_65);
x_80 = lean_array_uset(x_78, x_64, x_79);
lean_ctor_set(x_42, 1, x_80);
x_47 = x_42;
goto block_49;
}
block_49:
{
lean_object* x_48; 
x_48 = lean_array_fset(x_46, x_29, x_47);
x_31 = x_48;
goto block_37;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_87; uint64_t x_88; lean_object* x_89; uint64_t x_90; uint64_t x_91; uint64_t x_92; lean_object* x_93; uint64_t x_94; uint64_t x_95; uint64_t x_96; size_t x_97; size_t x_98; size_t x_99; size_t x_100; size_t x_101; lean_object* x_102; uint8_t x_103; 
x_81 = lean_ctor_get(x_42, 0);
x_82 = lean_ctor_get(x_42, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_42);
x_83 = lean_array_fset(x_38, x_29, x_41);
x_87 = lean_array_get_size(x_82);
x_88 = lean_uint64_of_nat(x_18);
x_89 = lean_unsigned_to_nat(32u);
x_90 = lean_uint64_of_nat(x_89);
x_91 = lean_uint64_shift_right(x_88, x_90);
x_92 = lean_uint64_xor(x_88, x_91);
x_93 = lean_unsigned_to_nat(16u);
x_94 = lean_uint64_of_nat(x_93);
x_95 = lean_uint64_shift_right(x_92, x_94);
x_96 = lean_uint64_xor(x_92, x_95);
x_97 = lean_uint64_to_usize(x_96);
x_98 = lean_usize_of_nat(x_87);
lean_dec(x_87);
x_99 = lean_usize_of_nat(x_13);
x_100 = lean_usize_sub(x_98, x_99);
x_101 = lean_usize_land(x_97, x_100);
x_102 = lean_array_uget(x_82, x_101);
x_103 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__0___redArg(x_18, x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_104 = lean_nat_add(x_81, x_13);
lean_dec(x_81);
x_105 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_105, 0, x_18);
lean_ctor_set(x_105, 1, x_27);
lean_ctor_set(x_105, 2, x_102);
x_106 = lean_array_uset(x_82, x_101, x_105);
x_107 = lean_unsigned_to_nat(2u);
x_108 = lean_nat_shiftl(x_104, x_107);
x_109 = lean_unsigned_to_nat(3u);
x_110 = lean_nat_div(x_108, x_109);
lean_dec(x_108);
x_111 = lean_array_get_size(x_106);
x_112 = lean_nat_dec_le(x_110, x_111);
lean_dec(x_111);
lean_dec(x_110);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
x_113 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__1___redArg(x_106);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_104);
lean_ctor_set(x_114, 1, x_113);
x_84 = x_114;
goto block_86;
}
else
{
lean_object* x_115; 
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_104);
lean_ctor_set(x_115, 1, x_106);
x_84 = x_115;
goto block_86;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_116 = lean_box(0);
x_117 = lean_array_uset(x_82, x_101, x_116);
x_118 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_UnreachableBranches_updateVarAssignment_spec__4___redArg(x_18, x_27, x_102);
x_119 = lean_array_uset(x_117, x_101, x_118);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_81);
lean_ctor_set(x_120, 1, x_119);
x_84 = x_120;
goto block_86;
}
block_86:
{
lean_object* x_85; 
x_85 = lean_array_fset(x_83, x_29, x_84);
x_31 = x_85;
goto block_37;
}
}
}
block_37:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_26, 2);
lean_inc(x_33);
lean_dec(x_26);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_33);
x_35 = lean_unbox(x_30);
x_5 = x_14;
x_6 = x_35;
x_8 = x_34;
goto _start;
}
}
else
{
lean_dec(x_27);
lean_dec(x_18);
x_5 = x_14;
x_8 = x_26;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_UnreachableBranches_updateJPParamsAssignment_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_foldM_loop___at___Lean_IR_UnreachableBranches_updateJPParamsAssignment_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_updateJPParamsAssignment(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_6 = l_Lean_IR_UnreachableBranches_markJPVisited(x_1, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_array_get_size(x_2);
x_10 = lean_unbox(x_7);
lean_dec(x_7);
lean_inc(x_9);
x_11 = l_Nat_foldM_loop___at___Lean_IR_UnreachableBranches_updateJPParamsAssignment_spec__0___redArg(x_2, x_3, x_4, x_9, x_9, x_10, x_4, x_8);
lean_dec(x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_UnreachableBranches_updateJPParamsAssignment_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_6);
lean_dec(x_6);
x_10 = l_Nat_foldM_loop___at___Lean_IR_UnreachableBranches_updateJPParamsAssignment_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_9, x_7, x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_UnreachableBranches_updateJPParamsAssignment_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_7);
lean_dec(x_7);
x_11 = l_Nat_foldM_loop___at___Lean_IR_UnreachableBranches_updateJPParamsAssignment_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_8, x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_updateJPParamsAssignment___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_UnreachableBranches_updateJPParamsAssignment(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_resetNestedJPParams_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_2);
x_9 = l_Lean_IR_UnreachableBranches_resetParamAssignment(x_8, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
x_4 = x_10;
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_6);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_resetNestedJPParams_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_15; 
x_15 = lean_usize_dec_eq(x_2, x_3);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_4);
x_16 = lean_array_uget(x_1, x_2);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l___private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_resetNestedJPParams(x_17, x_5, x_6);
lean_dec(x_17);
x_7 = x_18;
goto block_14;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l___private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_resetNestedJPParams(x_19, x_5, x_6);
lean_dec(x_19);
x_7 = x_20;
goto block_14;
}
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_6);
return x_21;
}
block_14:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_8;
x_6 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_resetNestedJPParams(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_6, x_7);
if (x_8 == 0)
{
lean_dec(x_7);
x_1 = x_5;
goto _start;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_7, x_7);
if (x_10 == 0)
{
lean_dec(x_7);
x_1 = x_5;
goto _start;
}
else
{
lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_box(0);
x_13 = lean_usize_of_nat(x_6);
x_14 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_15 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_resetNestedJPParams_spec__0(x_4, x_13, x_14, x_12, x_2, x_3);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_1 = x_5;
x_3 = x_16;
goto _start;
}
}
}
case 10:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_1, 3);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_get_size(x_18);
x_21 = lean_box(0);
x_22 = lean_nat_dec_lt(x_19, x_20);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_3);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_20, x_20);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_20);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_3);
return x_25;
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; 
x_26 = lean_usize_of_nat(x_19);
x_27 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_28 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_resetNestedJPParams_spec__1(x_18, x_26, x_27, x_21, x_2, x_3);
return x_28;
}
}
}
default: 
{
uint8_t x_29; 
x_29 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_29 == 0)
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_1, 3);
x_1 = x_30;
goto _start;
}
case 1:
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_1, 3);
x_1 = x_32;
goto _start;
}
case 2:
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_1, 3);
x_1 = x_34;
goto _start;
}
case 3:
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_1, 2);
x_1 = x_36;
goto _start;
}
case 4:
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_1, 3);
x_1 = x_38;
goto _start;
}
case 5:
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_1, 5);
x_1 = x_40;
goto _start;
}
case 6:
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_1, 2);
x_1 = x_42;
goto _start;
}
case 7:
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_1, 2);
x_1 = x_44;
goto _start;
}
case 8:
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_1, 1);
x_1 = x_46;
goto _start;
}
case 9:
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_1, 1);
x_1 = x_48;
goto _start;
}
default: 
{
goto _start;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_3);
return x_52;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_resetNestedJPParams_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_resetNestedJPParams_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_resetNestedJPParams_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_resetNestedJPParams_spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_resetNestedJPParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_resetNestedJPParams(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_UnreachableBranches_interpFnBody_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_15; uint8_t x_19; 
x_19 = lean_usize_dec_eq(x_3, x_4);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_5);
x_20 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_1);
x_23 = l_Lean_IR_UnreachableBranches_containsCtor(x_1, x_21);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_22);
x_24 = lean_box(0);
x_8 = x_24;
x_9 = x_7;
goto block_14;
}
else
{
lean_object* x_25; 
lean_inc(x_6);
x_25 = l_Lean_IR_UnreachableBranches_interpFnBody(x_22, x_6, x_7);
x_15 = x_25;
goto block_18;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_20, 0);
lean_inc(x_26);
lean_dec(x_20);
lean_inc(x_6);
x_27 = l_Lean_IR_UnreachableBranches_interpFnBody(x_26, x_6, x_7);
x_15 = x_27;
goto block_18;
}
}
else
{
lean_object* x_28; 
lean_dec(x_6);
lean_dec(x_1);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_7);
return x_28;
}
block_14:
{
lean_object* x_10; size_t x_11; size_t x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_3, x_11);
x_3 = x_12;
x_5 = x_8;
x_7 = x_9;
goto _start;
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_8 = x_16;
x_9 = x_17;
goto block_14;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_UnreachableBranches_interpFnBody_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_IR_instInhabitedFnBody;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_UnreachableBranches_interpFnBody_spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Array_instInhabited(lean_box(0));
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_interpFnBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
lean_inc(x_2);
x_7 = l_Lean_IR_UnreachableBranches_interpExpr(x_5, x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_IR_UnreachableBranches_updateVarAssignment(x_4, x_8, x_2, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_1 = x_6;
x_3 = x_11;
goto _start;
}
case 1:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_1, 2);
x_17 = lean_ctor_get(x_1, 3);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 3);
lean_inc(x_21);
lean_dec(x_2);
x_22 = l_Lean_IR_LocalContext_addJP(x_21, x_14, x_15, x_16);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 3, x_22);
lean_ctor_set(x_1, 2, x_20);
lean_ctor_set(x_1, 1, x_19);
lean_ctor_set(x_1, 0, x_18);
{
lean_object* _tmp_0 = x_17;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_ctor_get(x_1, 1);
x_26 = lean_ctor_get(x_1, 2);
x_27 = lean_ctor_get(x_1, 3);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_1);
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_2, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_2, 3);
lean_inc(x_31);
lean_dec(x_2);
x_32 = l_Lean_IR_LocalContext_addJP(x_31, x_24, x_25, x_26);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set(x_33, 3, x_32);
x_1 = x_27;
x_2 = x_33;
goto _start;
}
}
case 10:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_1, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 3);
lean_inc(x_36);
lean_dec(x_1);
x_37 = l_Lean_IR_UnreachableBranches_findVarValue(x_35, x_2, x_3);
lean_dec(x_35);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_array_get_size(x_36);
x_43 = lean_box(0);
x_44 = lean_nat_dec_lt(x_41, x_42);
if (x_44 == 0)
{
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_36);
lean_dec(x_2);
lean_ctor_set(x_37, 0, x_43);
return x_37;
}
else
{
uint8_t x_45; 
x_45 = lean_nat_dec_le(x_42, x_42);
if (x_45 == 0)
{
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_36);
lean_dec(x_2);
lean_ctor_set(x_37, 0, x_43);
return x_37;
}
else
{
size_t x_46; size_t x_47; lean_object* x_48; 
lean_free_object(x_37);
x_46 = lean_usize_of_nat(x_41);
x_47 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_48 = l_Array_foldlMUnsafe_fold___at___Lean_IR_UnreachableBranches_interpFnBody_spec__0(x_39, x_36, x_46, x_47, x_43, x_2, x_40);
lean_dec(x_36);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_49 = lean_ctor_get(x_37, 0);
x_50 = lean_ctor_get(x_37, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_37);
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_array_get_size(x_36);
x_53 = lean_box(0);
x_54 = lean_nat_dec_lt(x_51, x_52);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_36);
lean_dec(x_2);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_50);
return x_55;
}
else
{
uint8_t x_56; 
x_56 = lean_nat_dec_le(x_52, x_52);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_36);
lean_dec(x_2);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_53);
lean_ctor_set(x_57, 1, x_50);
return x_57;
}
else
{
size_t x_58; size_t x_59; lean_object* x_60; 
x_58 = lean_usize_of_nat(x_51);
x_59 = lean_usize_of_nat(x_52);
lean_dec(x_52);
x_60 = l_Array_foldlMUnsafe_fold___at___Lean_IR_UnreachableBranches_interpFnBody_spec__0(x_49, x_36, x_58, x_59, x_53, x_2, x_50);
lean_dec(x_36);
return x_60;
}
}
}
}
case 11:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_1, 0);
lean_inc(x_61);
lean_dec(x_1);
x_62 = l_Lean_IR_UnreachableBranches_findArgValue(x_61, x_2, x_3);
lean_dec(x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_IR_UnreachableBranches_updateCurrFnSummary(x_63, x_2, x_64);
return x_65;
}
case 12:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_84; lean_object* x_85; lean_object* x_96; 
x_66 = lean_ctor_get(x_1, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_1, 1);
lean_inc(x_67);
lean_dec(x_1);
x_84 = lean_ctor_get(x_2, 3);
lean_inc(x_84);
x_96 = l_Lean_IR_LocalContext_getJPParams(x_84, x_66);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_97 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
x_98 = lean_mk_string_unchecked("Option.get!", 11, 11);
x_99 = lean_unsigned_to_nat(21u);
x_100 = lean_unsigned_to_nat(14u);
x_101 = lean_mk_string_unchecked("value is none", 13, 13);
x_102 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_97, x_98, x_99, x_100, x_101);
lean_dec(x_101);
lean_dec(x_98);
lean_dec(x_97);
x_103 = l_panic___at___Lean_IR_UnreachableBranches_interpFnBody_spec__2(x_102);
x_85 = x_103;
goto block_95;
}
else
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_96, 0);
lean_inc(x_104);
lean_dec(x_96);
x_85 = x_104;
goto block_95;
}
block_83:
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_70 = l_Lean_IR_UnreachableBranches_updateJPParamsAssignment(x_66, x_68, x_67, x_2, x_3);
lean_dec(x_67);
lean_dec(x_68);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_unbox(x_71);
lean_dec(x_71);
if (x_72 == 0)
{
uint8_t x_73; 
lean_dec(x_69);
lean_dec(x_2);
x_73 = !lean_is_exclusive(x_70);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_70, 0);
lean_dec(x_74);
x_75 = lean_box(0);
lean_ctor_set(x_70, 0, x_75);
return x_70;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_70, 1);
lean_inc(x_76);
lean_dec(x_70);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_70, 1);
lean_inc(x_79);
lean_dec(x_70);
x_80 = l___private_Lean_Compiler_IR_ElimDeadBranches_0__Lean_IR_UnreachableBranches_resetNestedJPParams(x_69, x_2, x_79);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_1 = x_69;
x_3 = x_81;
goto _start;
}
}
block_95:
{
lean_object* x_86; 
x_86 = l_Lean_IR_LocalContext_getJPBody(x_84, x_66);
lean_dec(x_84);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_87 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
x_88 = lean_mk_string_unchecked("Option.get!", 11, 11);
x_89 = lean_unsigned_to_nat(21u);
x_90 = lean_unsigned_to_nat(14u);
x_91 = lean_mk_string_unchecked("value is none", 13, 13);
x_92 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_87, x_88, x_89, x_90, x_91);
lean_dec(x_91);
lean_dec(x_88);
lean_dec(x_87);
x_93 = l_panic___at___Lean_IR_UnreachableBranches_interpFnBody_spec__1(x_92);
x_68 = x_85;
x_69 = x_93;
goto block_83;
}
else
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_86, 0);
lean_inc(x_94);
lean_dec(x_86);
x_68 = x_85;
x_69 = x_94;
goto block_83;
}
}
}
default: 
{
uint8_t x_105; 
x_105 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_105 == 0)
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_1, 3);
lean_inc(x_106);
lean_dec(x_1);
x_1 = x_106;
goto _start;
}
case 1:
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_1, 3);
lean_inc(x_108);
lean_dec(x_1);
x_1 = x_108;
goto _start;
}
case 2:
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_1, 3);
lean_inc(x_110);
lean_dec(x_1);
x_1 = x_110;
goto _start;
}
case 3:
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_1, 2);
lean_inc(x_112);
lean_dec(x_1);
x_1 = x_112;
goto _start;
}
case 4:
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_1, 3);
lean_inc(x_114);
lean_dec(x_1);
x_1 = x_114;
goto _start;
}
case 5:
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_1, 5);
lean_inc(x_116);
lean_dec(x_1);
x_1 = x_116;
goto _start;
}
case 6:
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_1, 2);
lean_inc(x_118);
lean_dec(x_1);
x_1 = x_118;
goto _start;
}
case 7:
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_1, 2);
lean_inc(x_120);
lean_dec(x_1);
x_1 = x_120;
goto _start;
}
case 8:
{
lean_object* x_122; 
x_122 = lean_ctor_get(x_1, 1);
lean_inc(x_122);
lean_dec(x_1);
x_1 = x_122;
goto _start;
}
case 9:
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_1, 1);
lean_inc(x_124);
lean_dec(x_1);
x_1 = x_124;
goto _start;
}
default: 
{
goto _start;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_2);
lean_dec(x_1);
x_127 = lean_box(0);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_3);
return x_128;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_UnreachableBranches_interpFnBody_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at___Lean_IR_UnreachableBranches_interpFnBody_spec__0(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_UnreachableBranches_inferStep_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_5 = lean_box(0);
x_6 = lean_array_uset(x_3, x_2, x_5);
x_7 = lean_unsigned_to_nat(8u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_nat_shiftl(x_7, x_9);
x_11 = lean_unsigned_to_nat(3u);
x_12 = lean_nat_div(x_10, x_11);
lean_dec(x_10);
x_13 = l_Nat_nextPowerOfTwo(x_12);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = lean_mk_array(x_13, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_usize_of_nat(x_17);
x_19 = lean_usize_add(x_2, x_18);
x_20 = lean_array_uset(x_6, x_2, x_16);
x_2 = x_19;
x_3 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_UnreachableBranches_inferStep_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_5 = lean_box(0);
x_6 = lean_array_uset(x_3, x_2, x_5);
x_7 = lean_unsigned_to_nat(8u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_nat_shiftl(x_7, x_9);
x_11 = lean_unsigned_to_nat(3u);
x_12 = lean_nat_div(x_10, x_11);
lean_dec(x_10);
x_13 = l_Nat_nextPowerOfTwo(x_12);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = lean_mk_array(x_13, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_usize_of_nat(x_17);
x_19 = lean_usize_add(x_2, x_18);
x_20 = lean_array_uset(x_6, x_2, x_16);
x_2 = x_19;
x_3 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_UnreachableBranches_inferStep_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_2);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(1);
x_11 = l_Lean_IR_UnreachableBranches_updateVarAssignment(x_9, x_10, x_5, x_6);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_2, x_15);
x_2 = x_16;
x_4 = x_12;
x_6 = x_13;
goto _start;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_6);
return x_18;
}
}
}
LEAN_EXPORT uint8_t l_Nat_foldM_loop___at___Lean_IR_UnreachableBranches_inferStep_spec__3___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_nat_dec_lt(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_UnreachableBranches_inferStep_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_3, x_7);
if (x_8 == 1)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_3);
x_9 = lean_box(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_11 = lean_box(0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_3, x_13);
lean_dec(x_3);
x_35 = lean_nat_sub(x_2, x_14);
x_36 = lean_nat_sub(x_35, x_13);
lean_dec(x_35);
x_37 = lean_array_fget(x_12, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_50; lean_object* x_64; uint8_t x_65; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 3);
lean_inc(x_39);
lean_dec(x_37);
x_64 = lean_ctor_get(x_6, 1);
lean_inc(x_64);
x_65 = l_Nat_foldM_loop___at___Lean_IR_UnreachableBranches_inferStep_spec__3___redArg___lam__0(x_64, x_36);
if (x_65 == 0)
{
lean_object* x_66; 
lean_dec(x_64);
x_66 = l_outOfBounds___redArg(x_11);
x_50 = x_66;
goto block_63;
}
else
{
lean_object* x_67; 
x_67 = l_Lean_PersistentArray_get_x21___redArg(x_11, x_64, x_36);
x_50 = x_67;
goto block_63;
}
block_49:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = l_Lean_IR_UnreachableBranches_interpFnBody(x_39, x_40, x_42);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
x_46 = l_Nat_foldM_loop___at___Lean_IR_UnreachableBranches_inferStep_spec__3___redArg___lam__0(x_45, x_36);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_45);
lean_dec(x_36);
x_47 = l_outOfBounds___redArg(x_11);
x_15 = x_44;
x_16 = x_41;
x_17 = x_47;
goto block_24;
}
else
{
lean_object* x_48; 
x_48 = l_Lean_PersistentArray_get_x21___redArg(x_11, x_45, x_36);
lean_dec(x_36);
x_15 = x_44;
x_16 = x_41;
x_17 = x_48;
goto block_24;
}
}
block_63:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_51 = lean_array_get_size(x_38);
x_52 = lean_ctor_get(x_5, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_5, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_5, 3);
lean_inc(x_54);
lean_inc(x_36);
x_55 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_55, 0, x_36);
lean_ctor_set(x_55, 1, x_52);
lean_ctor_set(x_55, 2, x_53);
lean_ctor_set(x_55, 3, x_54);
x_56 = lean_nat_dec_lt(x_7, x_51);
if (x_56 == 0)
{
lean_dec(x_51);
lean_dec(x_38);
x_40 = x_55;
x_41 = x_50;
x_42 = x_6;
goto block_49;
}
else
{
uint8_t x_57; 
x_57 = lean_nat_dec_le(x_51, x_51);
if (x_57 == 0)
{
lean_dec(x_51);
lean_dec(x_38);
x_40 = x_55;
x_41 = x_50;
x_42 = x_6;
goto block_49;
}
else
{
lean_object* x_58; size_t x_59; size_t x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_box(0);
x_59 = lean_usize_of_nat(x_7);
x_60 = lean_usize_of_nat(x_51);
lean_dec(x_51);
x_61 = l_Array_foldlMUnsafe_fold___at___Lean_IR_UnreachableBranches_inferStep_spec__2(x_38, x_59, x_60, x_58, x_55, x_6);
lean_dec(x_38);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_40 = x_55;
x_41 = x_50;
x_42 = x_62;
goto block_49;
}
}
}
}
else
{
lean_object* x_68; lean_object* x_77; uint8_t x_78; 
lean_dec(x_37);
x_77 = lean_ctor_get(x_6, 1);
lean_inc(x_77);
x_78 = l_Nat_foldM_loop___at___Lean_IR_UnreachableBranches_inferStep_spec__3___redArg___lam__0(x_77, x_36);
if (x_78 == 0)
{
lean_object* x_79; 
lean_dec(x_77);
x_79 = l_outOfBounds___redArg(x_11);
x_68 = x_79;
goto block_76;
}
else
{
lean_object* x_80; 
x_80 = l_Lean_PersistentArray_get_x21___redArg(x_11, x_77, x_36);
x_68 = x_80;
goto block_76;
}
block_76:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_69 = lean_box(1);
lean_inc(x_5);
x_70 = l_Lean_IR_UnreachableBranches_updateCurrFnSummary(x_69, x_5, x_6);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
x_73 = l_Nat_foldM_loop___at___Lean_IR_UnreachableBranches_inferStep_spec__3___redArg___lam__0(x_72, x_36);
if (x_73 == 0)
{
lean_object* x_74; 
lean_dec(x_72);
lean_dec(x_36);
x_74 = l_outOfBounds___redArg(x_11);
x_25 = x_68;
x_26 = x_71;
x_27 = x_74;
goto block_34;
}
else
{
lean_object* x_75; 
x_75 = l_Lean_PersistentArray_get_x21___redArg(x_11, x_72, x_36);
lean_dec(x_36);
x_25 = x_68;
x_26 = x_71;
x_27 = x_75;
goto block_34;
}
}
}
block_24:
{
if (x_4 == 0)
{
uint8_t x_18; 
x_18 = l_Lean_IR_UnreachableBranches_Value_beq(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_box(1);
x_20 = lean_unbox(x_19);
x_3 = x_14;
x_4 = x_20;
x_6 = x_15;
goto _start;
}
else
{
x_3 = x_14;
x_6 = x_15;
goto _start;
}
}
else
{
lean_dec(x_17);
lean_dec(x_16);
x_3 = x_14;
x_6 = x_15;
goto _start;
}
}
block_34:
{
if (x_4 == 0)
{
uint8_t x_28; 
x_28 = l_Lean_IR_UnreachableBranches_Value_beq(x_25, x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_box(1);
x_30 = lean_unbox(x_29);
x_3 = x_14;
x_4 = x_30;
x_6 = x_26;
goto _start;
}
else
{
x_3 = x_14;
x_6 = x_26;
goto _start;
}
}
else
{
lean_dec(x_27);
lean_dec(x_25);
x_3 = x_14;
x_6 = x_26;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_UnreachableBranches_inferStep_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_foldM_loop___at___Lean_IR_UnreachableBranches_inferStep_spec__3___redArg(x_1, x_2, x_3, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_inferStep(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_array_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_usize_of_nat(x_5);
lean_inc(x_3);
x_7 = l_Array_mapMUnsafe_map___at___Lean_IR_UnreachableBranches_inferStep_spec__0(x_4, x_6, x_3);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_9 = l_Array_mapMUnsafe_map___at___Lean_IR_UnreachableBranches_inferStep_spec__1(x_4, x_6, x_3);
lean_inc(x_8);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
x_11 = lean_array_get_size(x_3);
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_14 = l_Nat_foldM_loop___at___Lean_IR_UnreachableBranches_inferStep_spec__3___redArg(x_1, x_11, x_11, x_13, x_1, x_10);
lean_dec(x_11);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_UnreachableBranches_inferStep_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_IR_UnreachableBranches_inferStep_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_UnreachableBranches_inferStep_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_IR_UnreachableBranches_inferStep_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_UnreachableBranches_inferStep_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_IR_UnreachableBranches_inferStep_spec__2(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_UnreachableBranches_inferStep_spec__3___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Nat_foldM_loop___at___Lean_IR_UnreachableBranches_inferStep_spec__3___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_UnreachableBranches_inferStep_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Nat_foldM_loop___at___Lean_IR_UnreachableBranches_inferStep_spec__3___redArg(x_1, x_2, x_3, x_7, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_UnreachableBranches_inferStep_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Nat_foldM_loop___at___Lean_IR_UnreachableBranches_inferStep_spec__3(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_inferStep___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_UnreachableBranches_inferStep(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_inferMain(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
lean_inc(x_1);
x_3 = l_Lean_IR_UnreachableBranches_inferStep(x_1, x_2);
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 0);
lean_dec(x_7);
x_8 = lean_box(0);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_2 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_UnreachableBranches_elimDeadAux_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_array_uget(x_5, x_4);
x_8 = lean_box(0);
x_9 = lean_array_uset(x_5, x_4, x_8);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_7, 0);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_inc(x_1);
x_20 = l_Lean_IR_UnreachableBranches_containsCtor(x_1, x_18);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_19);
x_21 = lean_box(13);
lean_ctor_set(x_7, 1, x_21);
x_10 = x_7;
goto block_16;
}
else
{
lean_object* x_22; 
x_22 = l_Lean_IR_UnreachableBranches_elimDeadAux(x_2, x_19);
lean_ctor_set(x_7, 1, x_22);
x_10 = x_7;
goto block_16;
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_7, 0);
x_24 = lean_ctor_get(x_7, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_7);
lean_inc(x_23);
lean_inc(x_1);
x_25 = l_Lean_IR_UnreachableBranches_containsCtor(x_1, x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_24);
x_26 = lean_box(13);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
x_10 = x_27;
goto block_16;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_Lean_IR_UnreachableBranches_elimDeadAux(x_2, x_24);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_28);
x_10 = x_29;
goto block_16;
}
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_7);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_7, 0);
x_32 = l_Lean_IR_UnreachableBranches_elimDeadAux(x_2, x_31);
lean_ctor_set(x_7, 0, x_32);
x_10 = x_7;
goto block_16;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_7, 0);
lean_inc(x_33);
lean_dec(x_7);
x_34 = l_Lean_IR_UnreachableBranches_elimDeadAux(x_2, x_33);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_10 = x_35;
goto block_16;
}
}
block_16:
{
lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_4, x_12);
x_14 = lean_array_uset(x_9, x_4, x_10);
x_4 = x_13;
x_5 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_elimDeadAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 3);
x_11 = l_Lean_IR_UnreachableBranches_elimDeadAux(x_1, x_10);
lean_ctor_set(x_2, 3, x_11);
return x_2;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
x_15 = lean_ctor_get(x_2, 3);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_16 = l_Lean_IR_UnreachableBranches_elimDeadAux(x_1, x_15);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_17, 2, x_14);
lean_ctor_set(x_17, 3, x_16);
return x_17;
}
}
case 1:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_2, 2);
x_20 = lean_ctor_get(x_2, 3);
x_21 = l_Lean_IR_UnreachableBranches_elimDeadAux(x_1, x_19);
x_22 = l_Lean_IR_UnreachableBranches_elimDeadAux(x_1, x_20);
lean_ctor_set(x_2, 3, x_22);
lean_ctor_set(x_2, 2, x_21);
return x_2;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_ctor_get(x_2, 2);
x_26 = lean_ctor_get(x_2, 3);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_2);
x_27 = l_Lean_IR_UnreachableBranches_elimDeadAux(x_1, x_25);
x_28 = l_Lean_IR_UnreachableBranches_elimDeadAux(x_1, x_26);
x_29 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_27);
lean_ctor_set(x_29, 3, x_28);
return x_29;
}
}
case 10:
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_2);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint64_t x_36; lean_object* x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; lean_object* x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; size_t x_45; size_t x_46; lean_object* x_47; size_t x_48; size_t x_49; size_t x_50; lean_object* x_51; lean_object* x_52; size_t x_53; lean_object* x_54; size_t x_55; lean_object* x_56; 
x_31 = lean_ctor_get(x_2, 1);
x_32 = lean_ctor_get(x_2, 3);
x_33 = lean_ctor_get(x_1, 1);
x_34 = lean_box(0);
x_35 = lean_array_get_size(x_33);
x_36 = lean_uint64_of_nat(x_31);
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
x_51 = lean_array_uget(x_33, x_50);
x_52 = l_Std_DHashMap_Internal_AssocList_getD___at___Lean_IR_UnreachableBranches_findVarValue_spec__0___redArg(x_31, x_34, x_51);
lean_dec(x_51);
x_53 = lean_array_size(x_32);
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_usize_of_nat(x_54);
x_56 = l_Array_mapMUnsafe_map___at___Lean_IR_UnreachableBranches_elimDeadAux_spec__0(x_52, x_1, x_53, x_55, x_32);
lean_ctor_set(x_2, 3, x_56);
return x_2;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint64_t x_64; lean_object* x_65; uint64_t x_66; uint64_t x_67; uint64_t x_68; lean_object* x_69; uint64_t x_70; uint64_t x_71; uint64_t x_72; size_t x_73; size_t x_74; lean_object* x_75; size_t x_76; size_t x_77; size_t x_78; lean_object* x_79; lean_object* x_80; size_t x_81; lean_object* x_82; size_t x_83; lean_object* x_84; lean_object* x_85; 
x_57 = lean_ctor_get(x_2, 0);
x_58 = lean_ctor_get(x_2, 1);
x_59 = lean_ctor_get(x_2, 2);
x_60 = lean_ctor_get(x_2, 3);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_2);
x_61 = lean_ctor_get(x_1, 1);
x_62 = lean_box(0);
x_63 = lean_array_get_size(x_61);
x_64 = lean_uint64_of_nat(x_58);
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
x_79 = lean_array_uget(x_61, x_78);
x_80 = l_Std_DHashMap_Internal_AssocList_getD___at___Lean_IR_UnreachableBranches_findVarValue_spec__0___redArg(x_58, x_62, x_79);
lean_dec(x_79);
x_81 = lean_array_size(x_60);
x_82 = lean_unsigned_to_nat(0u);
x_83 = lean_usize_of_nat(x_82);
x_84 = l_Array_mapMUnsafe_map___at___Lean_IR_UnreachableBranches_elimDeadAux_spec__0(x_80, x_1, x_81, x_83, x_60);
x_85 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_85, 0, x_57);
lean_ctor_set(x_85, 1, x_58);
lean_ctor_set(x_85, 2, x_59);
lean_ctor_set(x_85, 3, x_84);
return x_85;
}
}
default: 
{
uint8_t x_86; 
x_86 = l_Lean_IR_FnBody_isTerminal(x_2);
if (x_86 == 0)
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_2, 3);
lean_inc(x_87);
x_3 = x_87;
goto block_8;
}
case 1:
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_2, 3);
lean_inc(x_88);
x_3 = x_88;
goto block_8;
}
case 2:
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_2, 3);
lean_inc(x_89);
x_3 = x_89;
goto block_8;
}
case 3:
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_2, 2);
lean_inc(x_90);
x_3 = x_90;
goto block_8;
}
case 4:
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_2, 3);
lean_inc(x_91);
x_3 = x_91;
goto block_8;
}
case 5:
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_2, 5);
lean_inc(x_92);
x_3 = x_92;
goto block_8;
}
case 6:
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_2, 2);
lean_inc(x_93);
x_3 = x_93;
goto block_8;
}
case 7:
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_2, 2);
lean_inc(x_94);
x_3 = x_94;
goto block_8;
}
case 8:
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_2, 1);
lean_inc(x_95);
x_3 = x_95;
goto block_8;
}
case 9:
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_2, 1);
lean_inc(x_96);
x_3 = x_96;
goto block_8;
}
default: 
{
lean_inc(x_2);
x_3 = x_2;
goto block_8;
}
}
}
else
{
return x_2;
}
}
}
block_8:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(13);
x_5 = l_Lean_IR_FnBody_setBody(x_2, x_4);
x_6 = l_Lean_IR_UnreachableBranches_elimDeadAux(x_1, x_3);
x_7 = l_Lean_IR_FnBody_setBody(x_5, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_UnreachableBranches_elimDeadAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___at___Lean_IR_UnreachableBranches_elimDeadAux_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_elimDeadAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_UnreachableBranches_elimDeadAux(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_elimDead(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 3);
lean_inc(x_3);
x_4 = l_Lean_IR_UnreachableBranches_elimDeadAux(x_1, x_3);
x_5 = l_Lean_IR_Decl_updateBody_x21(x_2, x_4);
return x_5;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UnreachableBranches_elimDead___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_UnreachableBranches_elimDead(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at___Lean_IR_elimDeadBranches_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 1)
{
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_22; lean_object* x_23; 
x_8 = lean_box(0);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_4, x_9);
x_11 = lean_nat_sub(x_3, x_4);
lean_dec(x_4);
x_22 = lean_array_fget(x_1, x_11);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_12 = x_23;
goto block_21;
block_21:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
x_14 = lean_nat_dec_lt(x_11, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
x_15 = l_outOfBounds___redArg(x_8);
x_16 = l_Lean_IR_UnreachableBranches_addFunctionSummary(x_5, x_12, x_15);
x_4 = x_10;
x_5 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_inc(x_2);
x_18 = l_Lean_PersistentArray_get_x21___redArg(x_8, x_2, x_11);
lean_dec(x_11);
x_19 = l_Lean_IR_UnreachableBranches_addFunctionSummary(x_5, x_12, x_18);
x_4 = x_10;
x_5 = x_19;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at___Lean_IR_elimDeadBranches_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_foldTR_loop___at___Lean_IR_elimDeadBranches_spec__0___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_IR_elimDeadBranches_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_3, x_6);
if (x_7 == 1)
{
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = l_Lean_IR_instBEqVarId;
x_9 = lean_alloc_closure((void*)(l_Lean_IR_instHashableVarId___lam__0___boxed), 1, 0);
x_10 = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), x_8, x_9);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_3, x_11);
lean_dec(x_3);
x_13 = lean_array_fget(x_2, x_4);
x_14 = lean_array_get(x_10, x_1, x_4);
x_15 = l_Lean_IR_UnreachableBranches_elimDead(x_14, x_13);
lean_dec(x_14);
x_16 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_17 = lean_array_push(x_5, x_15);
x_3 = x_12;
x_4 = x_16;
x_5 = x_17;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_IR_elimDeadBranches_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_mapFinIdxM_map___at___Lean_IR_elimDeadBranches_spec__1___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_elimDeadBranches___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_array_size(x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_usize_of_nat(x_5);
lean_inc(x_1);
x_7 = l_Array_mapMUnsafe_map___at___Lean_IR_UnreachableBranches_inferStep_spec__0(x_4, x_6, x_1);
x_8 = lean_array_get_size(x_1);
x_9 = lean_box(0);
lean_inc(x_8);
x_10 = l_Lean_mkPersistentArray(lean_box(0), x_8, x_9);
lean_inc(x_1);
x_11 = l_Array_mapMUnsafe_map___at___Lean_IR_UnreachableBranches_inferStep_spec__1(x_4, x_6, x_1);
x_12 = lean_box(0);
lean_inc(x_3);
lean_inc(x_1);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_1);
lean_ctor_set(x_13, 2, x_3);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_10);
lean_ctor_set(x_14, 2, x_11);
x_15 = l_Lean_IR_UnreachableBranches_inferMain(x_13, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_15, 1);
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
lean_inc(x_8);
x_21 = l_Nat_foldTR_loop___at___Lean_IR_elimDeadBranches_spec__0___redArg(x_1, x_19, x_8, x_8, x_3);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_dec(x_2);
lean_ctor_set(x_15, 1, x_22);
lean_ctor_set(x_15, 0, x_21);
x_23 = lean_mk_empty_array_with_capacity(x_8);
x_24 = l_Array_mapFinIdxM_map___at___Lean_IR_elimDeadBranches_spec__1___redArg(x_20, x_1, x_8, x_5, x_23);
lean_dec(x_1);
lean_dec(x_20);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_15);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_dec(x_15);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_8);
x_29 = l_Nat_foldTR_loop___at___Lean_IR_elimDeadBranches_spec__0___redArg(x_1, x_27, x_8, x_8, x_3);
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
lean_dec(x_2);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_mk_empty_array_with_capacity(x_8);
x_33 = l_Array_mapFinIdxM_map___at___Lean_IR_elimDeadBranches_spec__1___redArg(x_28, x_1, x_8, x_5, x_32);
lean_dec(x_1);
lean_dec(x_28);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_elimDeadBranches(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_elimDeadBranches___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at___Lean_IR_elimDeadBranches_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_foldTR_loop___at___Lean_IR_elimDeadBranches_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at___Lean_IR_elimDeadBranches_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_foldTR_loop___at___Lean_IR_elimDeadBranches_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_IR_elimDeadBranches_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_mapFinIdxM_map___at___Lean_IR_elimDeadBranches_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_IR_elimDeadBranches_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_mapFinIdxM_map___at___Lean_IR_elimDeadBranches_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_elimDeadBranches___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_elimDeadBranches(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Lean_Compiler_IR_Format(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_ElimDeadBranches(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_IR_Format(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_UnreachableBranches_instInhabitedValue = _init_l_Lean_IR_UnreachableBranches_instInhabitedValue();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_instInhabitedValue);
l_Lean_IR_UnreachableBranches_instReprValue = _init_l_Lean_IR_UnreachableBranches_instReprValue();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_instReprValue);
l_Lean_IR_UnreachableBranches_instToFormatValue = _init_l_Lean_IR_UnreachableBranches_instToFormatValue();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_instToFormatValue);
l_Lean_IR_UnreachableBranches_instToStringValue = _init_l_Lean_IR_UnreachableBranches_instToStringValue();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_instToStringValue);
l_Lean_IR_UnreachableBranches_Value_instBEq = _init_l_Lean_IR_UnreachableBranches_Value_instBEq();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_Value_instBEq);
l_Lean_IR_UnreachableBranches_Value_instToFormat = _init_l_Lean_IR_UnreachableBranches_Value_instToFormat();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_Value_instToFormat);
l_Lean_IR_UnreachableBranches_Value_instToString = _init_l_Lean_IR_UnreachableBranches_Value_instToString();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_Value_instToString);
l_Lean_IR_UnreachableBranches_Value_truncateMaxDepth = _init_l_Lean_IR_UnreachableBranches_Value_truncateMaxDepth();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_Value_truncateMaxDepth);
if (builtin) {res = l_Lean_IR_UnreachableBranches_initFn____x40_Lean_Compiler_IR_ElimDeadBranches___hyg_1177_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_IR_UnreachableBranches_functionSummariesExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_IR_UnreachableBranches_functionSummariesExt);
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
