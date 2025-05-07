// Lean compiler output
// Module: Lean.Meta.Closure
// Imports: Lean.MetavarContext Lean.Environment Lean.AddDecl Lean.Util.FoldConsts Lean.Meta.Basic Lean.Meta.Check Lean.Meta.Tactic.AuxLemma
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Closure_preprocess_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
uint8_t l_ptrEqList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferrringUnsafe___at___Lean_Meta_mkAuxDefinition_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcessAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_Closure_collectExprAux_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectLevelAux_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_Closure_collectExprAux_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_hasParam(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldRev___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_ExprStructEq_hash___boxed(lean_object*);
lean_object* l_Array_reverse(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitLevel(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelMax_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_replaceFVarId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_compileDecl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectLevelAux_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectLevelAux_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_instInhabitedToProcessElement;
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___Lean_Meta_Closure_process_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_Closure_collectExprAux_spec__3___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Closure_preprocess_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Meta_Closure_collectExprAux_spec__0_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Meta_getZetaDeltaFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___Lean_Meta_Closure_process_spec__0(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Meta_mkAuxLemma(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___Lean_Meta_Closure_collectExprAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Closure_preprocess_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_Lean_getMaxHeight(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getValue_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2_spec__2_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_Closure_collectExprAux_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___Lean_Expr_appFn_x21_spec__0(lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Meta_Closure_collectExprAux_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2(lean_object*, lean_object*);
lean_object* l_Array_back_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_Closure_collectExprAux_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___Lean_Meta_Closure_process_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_Closure_collectExprAux_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___Lean_Meta_Closure_collectExprAux_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_simpLevelIMax_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall(lean_object*, lean_object*);
lean_object* lean_expr_lower_loose_bvars(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___Lean_Meta_Closure_collectExprAux_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxTheorem(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___Lean_Meta_Closure_collectExprAux_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Closure_mkLambda_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Closure_mkLambda_spec__0(size_t, size_t, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferrringUnsafe___at___Lean_Meta_mkAuxDefinition_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_Closure_collectExprAux_spec__3___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___Lean_Meta_Closure_collectExprAux_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectLevelAux_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferrringUnsafe___at___Lean_Meta_mkAuxDefinition_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_resetZetaDeltaFVarIds___redArg(lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_ExprStructEq_instBEq;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_LocalContext_get_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitExpr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Closure_process_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
uint64_t l_Lean_Level_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferrringUnsafe___at___Lean_Meta_mkAuxDefinition_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_hasLevelParam(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_Closure_collectExprAux_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
extern lean_object* l_Lean_Level_instHashable;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Closure_process_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___Lean_Meta_Closure_collectExprAux_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectLevelAux_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Level_instBEq;
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___Lean_Meta_Closure_process_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_simpLevelMax_x27(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_Closure_collectExprAux_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_Closure_collectExprAux_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectLevelAux_spec__5___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Closure_preprocess_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(uint8_t, uint8_t);
static lean_object* _init_l_Lean_Meta_Closure_instInhabitedToProcessElement() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitLevel(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_176; 
x_176 = l_Lean_Level_hasMVar(x_2);
if (x_176 == 0)
{
uint8_t x_177; 
x_177 = l_Lean_Level_hasParam(x_2);
if (x_177 == 0)
{
lean_object* x_178; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_2);
lean_ctor_set(x_178, 1, x_9);
return x_178;
}
else
{
goto block_175;
}
}
else
{
goto block_175;
}
block_31:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_10, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_10, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_10, 4);
lean_inc(x_17);
x_18 = lean_ctor_get(x_10, 5);
lean_inc(x_18);
x_19 = lean_ctor_get(x_10, 6);
lean_inc(x_19);
x_20 = lean_ctor_get(x_10, 7);
lean_inc(x_20);
x_21 = lean_ctor_get(x_10, 8);
lean_inc(x_21);
x_22 = lean_ctor_get(x_10, 9);
lean_inc(x_22);
x_23 = lean_ctor_get(x_10, 10);
lean_inc(x_23);
x_24 = lean_ctor_get(x_10, 11);
lean_inc(x_24);
lean_dec(x_10);
x_25 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_14);
lean_ctor_set(x_25, 2, x_15);
lean_ctor_set(x_25, 3, x_16);
lean_ctor_set(x_25, 4, x_17);
lean_ctor_set(x_25, 5, x_18);
lean_ctor_set(x_25, 6, x_19);
lean_ctor_set(x_25, 7, x_20);
lean_ctor_set(x_25, 8, x_21);
lean_ctor_set(x_25, 9, x_22);
lean_ctor_set(x_25, 10, x_23);
lean_ctor_set(x_25, 11, x_24);
x_26 = lean_st_ref_set(x_4, x_25, x_11);
lean_dec(x_4);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_12);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_12);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
block_175:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_st_ref_get(x_4, x_9);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint64_t x_41; lean_object* x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; lean_object* x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; size_t x_50; size_t x_51; lean_object* x_52; size_t x_53; size_t x_54; size_t x_55; lean_object* x_56; lean_object* x_57; 
x_36 = lean_ctor_get(x_32, 1);
x_37 = lean_ctor_get(x_32, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = l_Lean_Level_instBEq;
x_40 = lean_array_get_size(x_38);
x_41 = l_Lean_Level_hash(x_2);
x_42 = lean_unsigned_to_nat(32u);
x_43 = lean_uint64_of_nat(x_42);
x_44 = lean_uint64_shift_right(x_41, x_43);
x_45 = lean_uint64_xor(x_41, x_44);
x_46 = lean_unsigned_to_nat(16u);
x_47 = lean_uint64_of_nat(x_46);
x_48 = lean_uint64_shift_right(x_45, x_47);
x_49 = lean_uint64_xor(x_45, x_48);
x_50 = lean_uint64_to_usize(x_49);
x_51 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_usize_of_nat(x_52);
x_54 = lean_usize_sub(x_51, x_53);
x_55 = lean_usize_land(x_50, x_54);
x_56 = lean_array_uget(x_38, x_55);
lean_dec(x_38);
lean_inc(x_2);
x_57 = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(x_39, x_2, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_free_object(x_32);
x_58 = lean_box(x_3);
lean_inc(x_4);
lean_inc(x_2);
x_59 = lean_apply_8(x_1, x_2, x_58, x_4, x_5, x_6, x_7, x_8, x_36);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_st_ref_take(x_4, x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = !lean_is_exclusive(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; size_t x_70; size_t x_71; size_t x_72; lean_object* x_73; uint8_t x_74; 
x_67 = lean_ctor_get(x_64, 0);
x_68 = lean_ctor_get(x_64, 1);
x_69 = lean_array_get_size(x_68);
x_70 = lean_usize_of_nat(x_69);
lean_dec(x_69);
x_71 = lean_usize_sub(x_70, x_53);
x_72 = lean_usize_land(x_50, x_71);
x_73 = lean_array_uget(x_68, x_72);
lean_inc(x_73);
lean_inc(x_2);
x_74 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_39, x_2, x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_75 = lean_nat_add(x_67, x_52);
lean_dec(x_67);
lean_inc(x_60);
x_76 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_76, 0, x_2);
lean_ctor_set(x_76, 1, x_60);
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
x_84 = l_Lean_Level_instHashable;
x_85 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_84, x_77);
lean_ctor_set(x_64, 1, x_85);
lean_ctor_set(x_64, 0, x_75);
x_10 = x_63;
x_11 = x_65;
x_12 = x_60;
x_13 = x_64;
goto block_31;
}
else
{
lean_ctor_set(x_64, 1, x_77);
lean_ctor_set(x_64, 0, x_75);
x_10 = x_63;
x_11 = x_65;
x_12 = x_60;
x_13 = x_64;
goto block_31;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_box(0);
x_87 = lean_array_uset(x_68, x_72, x_86);
lean_inc(x_60);
x_88 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_39, x_2, x_60, x_73);
x_89 = lean_array_uset(x_87, x_72, x_88);
lean_ctor_set(x_64, 1, x_89);
x_10 = x_63;
x_11 = x_65;
x_12 = x_60;
x_13 = x_64;
goto block_31;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; size_t x_93; size_t x_94; size_t x_95; lean_object* x_96; uint8_t x_97; 
x_90 = lean_ctor_get(x_64, 0);
x_91 = lean_ctor_get(x_64, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_64);
x_92 = lean_array_get_size(x_91);
x_93 = lean_usize_of_nat(x_92);
lean_dec(x_92);
x_94 = lean_usize_sub(x_93, x_53);
x_95 = lean_usize_land(x_50, x_94);
x_96 = lean_array_uget(x_91, x_95);
lean_inc(x_96);
lean_inc(x_2);
x_97 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_39, x_2, x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_98 = lean_nat_add(x_90, x_52);
lean_dec(x_90);
lean_inc(x_60);
x_99 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_99, 0, x_2);
lean_ctor_set(x_99, 1, x_60);
lean_ctor_set(x_99, 2, x_96);
x_100 = lean_array_uset(x_91, x_95, x_99);
x_101 = lean_unsigned_to_nat(2u);
x_102 = lean_nat_shiftl(x_98, x_101);
x_103 = lean_unsigned_to_nat(3u);
x_104 = lean_nat_div(x_102, x_103);
lean_dec(x_102);
x_105 = lean_array_get_size(x_100);
x_106 = lean_nat_dec_le(x_104, x_105);
lean_dec(x_105);
lean_dec(x_104);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = l_Lean_Level_instHashable;
x_108 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_107, x_100);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_98);
lean_ctor_set(x_109, 1, x_108);
x_10 = x_63;
x_11 = x_65;
x_12 = x_60;
x_13 = x_109;
goto block_31;
}
else
{
lean_object* x_110; 
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_98);
lean_ctor_set(x_110, 1, x_100);
x_10 = x_63;
x_11 = x_65;
x_12 = x_60;
x_13 = x_110;
goto block_31;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_111 = lean_box(0);
x_112 = lean_array_uset(x_91, x_95, x_111);
lean_inc(x_60);
x_113 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_39, x_2, x_60, x_96);
x_114 = lean_array_uset(x_112, x_95, x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_90);
lean_ctor_set(x_115, 1, x_114);
x_10 = x_63;
x_11 = x_65;
x_12 = x_60;
x_13 = x_115;
goto block_31;
}
}
}
else
{
lean_dec(x_4);
lean_dec(x_2);
return x_59;
}
}
else
{
lean_object* x_116; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_116 = lean_ctor_get(x_57, 0);
lean_inc(x_116);
lean_dec(x_57);
lean_ctor_set(x_32, 0, x_116);
return x_32;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint64_t x_121; lean_object* x_122; uint64_t x_123; uint64_t x_124; uint64_t x_125; lean_object* x_126; uint64_t x_127; uint64_t x_128; uint64_t x_129; size_t x_130; size_t x_131; lean_object* x_132; size_t x_133; size_t x_134; size_t x_135; lean_object* x_136; lean_object* x_137; 
x_117 = lean_ctor_get(x_32, 1);
lean_inc(x_117);
lean_dec(x_32);
x_118 = lean_ctor_get(x_34, 1);
lean_inc(x_118);
lean_dec(x_34);
x_119 = l_Lean_Level_instBEq;
x_120 = lean_array_get_size(x_118);
x_121 = l_Lean_Level_hash(x_2);
x_122 = lean_unsigned_to_nat(32u);
x_123 = lean_uint64_of_nat(x_122);
x_124 = lean_uint64_shift_right(x_121, x_123);
x_125 = lean_uint64_xor(x_121, x_124);
x_126 = lean_unsigned_to_nat(16u);
x_127 = lean_uint64_of_nat(x_126);
x_128 = lean_uint64_shift_right(x_125, x_127);
x_129 = lean_uint64_xor(x_125, x_128);
x_130 = lean_uint64_to_usize(x_129);
x_131 = lean_usize_of_nat(x_120);
lean_dec(x_120);
x_132 = lean_unsigned_to_nat(1u);
x_133 = lean_usize_of_nat(x_132);
x_134 = lean_usize_sub(x_131, x_133);
x_135 = lean_usize_land(x_130, x_134);
x_136 = lean_array_uget(x_118, x_135);
lean_dec(x_118);
lean_inc(x_2);
x_137 = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(x_119, x_2, x_136);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_box(x_3);
lean_inc(x_4);
lean_inc(x_2);
x_139 = lean_apply_8(x_1, x_2, x_138, x_4, x_5, x_6, x_7, x_8, x_117);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; size_t x_150; size_t x_151; size_t x_152; lean_object* x_153; uint8_t x_154; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_142 = lean_st_ref_take(x_4, x_141);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
lean_dec(x_142);
x_146 = lean_ctor_get(x_144, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_144, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_148 = x_144;
} else {
 lean_dec_ref(x_144);
 x_148 = lean_box(0);
}
x_149 = lean_array_get_size(x_147);
x_150 = lean_usize_of_nat(x_149);
lean_dec(x_149);
x_151 = lean_usize_sub(x_150, x_133);
x_152 = lean_usize_land(x_130, x_151);
x_153 = lean_array_uget(x_147, x_152);
lean_inc(x_153);
lean_inc(x_2);
x_154 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_119, x_2, x_153);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_155 = lean_nat_add(x_146, x_132);
lean_dec(x_146);
lean_inc(x_140);
x_156 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_156, 0, x_2);
lean_ctor_set(x_156, 1, x_140);
lean_ctor_set(x_156, 2, x_153);
x_157 = lean_array_uset(x_147, x_152, x_156);
x_158 = lean_unsigned_to_nat(2u);
x_159 = lean_nat_shiftl(x_155, x_158);
x_160 = lean_unsigned_to_nat(3u);
x_161 = lean_nat_div(x_159, x_160);
lean_dec(x_159);
x_162 = lean_array_get_size(x_157);
x_163 = lean_nat_dec_le(x_161, x_162);
lean_dec(x_162);
lean_dec(x_161);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = l_Lean_Level_instHashable;
x_165 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_164, x_157);
if (lean_is_scalar(x_148)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_148;
}
lean_ctor_set(x_166, 0, x_155);
lean_ctor_set(x_166, 1, x_165);
x_10 = x_143;
x_11 = x_145;
x_12 = x_140;
x_13 = x_166;
goto block_31;
}
else
{
lean_object* x_167; 
if (lean_is_scalar(x_148)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_148;
}
lean_ctor_set(x_167, 0, x_155);
lean_ctor_set(x_167, 1, x_157);
x_10 = x_143;
x_11 = x_145;
x_12 = x_140;
x_13 = x_167;
goto block_31;
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_168 = lean_box(0);
x_169 = lean_array_uset(x_147, x_152, x_168);
lean_inc(x_140);
x_170 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_119, x_2, x_140, x_153);
x_171 = lean_array_uset(x_169, x_152, x_170);
if (lean_is_scalar(x_148)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_148;
}
lean_ctor_set(x_172, 0, x_146);
lean_ctor_set(x_172, 1, x_171);
x_10 = x_143;
x_11 = x_145;
x_12 = x_140;
x_13 = x_172;
goto block_31;
}
}
else
{
lean_dec(x_4);
lean_dec(x_2);
return x_139;
}
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_173 = lean_ctor_get(x_137, 0);
lean_inc(x_173);
lean_dec(x_137);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_117);
return x_174;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitLevel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Meta_Closure_visitLevel(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitExpr(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_179; 
x_179 = l_Lean_Expr_hasLevelParam(x_2);
if (x_179 == 0)
{
uint8_t x_180; 
x_180 = l_Lean_Expr_hasFVar(x_2);
if (x_180 == 0)
{
uint8_t x_181; 
x_181 = l_Lean_Expr_hasMVar(x_2);
if (x_181 == 0)
{
lean_object* x_182; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_2);
lean_ctor_set(x_182, 1, x_9);
return x_182;
}
else
{
goto block_178;
}
}
else
{
goto block_178;
}
}
else
{
goto block_178;
}
block_31:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_15 = lean_ctor_get(x_11, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_11, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_11, 4);
lean_inc(x_17);
x_18 = lean_ctor_get(x_11, 5);
lean_inc(x_18);
x_19 = lean_ctor_get(x_11, 6);
lean_inc(x_19);
x_20 = lean_ctor_get(x_11, 7);
lean_inc(x_20);
x_21 = lean_ctor_get(x_11, 8);
lean_inc(x_21);
x_22 = lean_ctor_get(x_11, 9);
lean_inc(x_22);
x_23 = lean_ctor_get(x_11, 10);
lean_inc(x_23);
x_24 = lean_ctor_get(x_11, 11);
lean_inc(x_24);
lean_dec(x_11);
x_25 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_14);
lean_ctor_set(x_25, 2, x_15);
lean_ctor_set(x_25, 3, x_16);
lean_ctor_set(x_25, 4, x_17);
lean_ctor_set(x_25, 5, x_18);
lean_ctor_set(x_25, 6, x_19);
lean_ctor_set(x_25, 7, x_20);
lean_ctor_set(x_25, 8, x_21);
lean_ctor_set(x_25, 9, x_22);
lean_ctor_set(x_25, 10, x_23);
lean_ctor_set(x_25, 11, x_24);
x_26 = lean_st_ref_set(x_4, x_25, x_10);
lean_dec(x_4);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_12);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_12);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
block_178:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_st_ref_get(x_4, x_9);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint64_t x_41; lean_object* x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; lean_object* x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; size_t x_50; size_t x_51; lean_object* x_52; size_t x_53; size_t x_54; size_t x_55; lean_object* x_56; lean_object* x_57; 
x_36 = lean_ctor_get(x_32, 1);
x_37 = lean_ctor_get(x_32, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = l_Lean_ExprStructEq_instBEq;
x_40 = lean_array_get_size(x_38);
x_41 = l_Lean_Expr_hash(x_2);
x_42 = lean_unsigned_to_nat(32u);
x_43 = lean_uint64_of_nat(x_42);
x_44 = lean_uint64_shift_right(x_41, x_43);
x_45 = lean_uint64_xor(x_41, x_44);
x_46 = lean_unsigned_to_nat(16u);
x_47 = lean_uint64_of_nat(x_46);
x_48 = lean_uint64_shift_right(x_45, x_47);
x_49 = lean_uint64_xor(x_45, x_48);
x_50 = lean_uint64_to_usize(x_49);
x_51 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_usize_of_nat(x_52);
x_54 = lean_usize_sub(x_51, x_53);
x_55 = lean_usize_land(x_50, x_54);
x_56 = lean_array_uget(x_38, x_55);
lean_dec(x_38);
lean_inc(x_2);
x_57 = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(x_39, x_2, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_free_object(x_32);
x_58 = lean_box(x_3);
lean_inc(x_4);
lean_inc(x_2);
x_59 = lean_apply_8(x_1, x_2, x_58, x_4, x_5, x_6, x_7, x_8, x_36);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_st_ref_take(x_4, x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = !lean_is_exclusive(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; size_t x_71; size_t x_72; size_t x_73; lean_object* x_74; uint8_t x_75; 
x_67 = lean_ctor_get(x_64, 0);
x_68 = lean_ctor_get(x_64, 1);
x_69 = lean_ctor_get(x_63, 0);
lean_inc(x_69);
x_70 = lean_array_get_size(x_68);
x_71 = lean_usize_of_nat(x_70);
lean_dec(x_70);
x_72 = lean_usize_sub(x_71, x_53);
x_73 = lean_usize_land(x_50, x_72);
x_74 = lean_array_uget(x_68, x_73);
lean_inc(x_74);
lean_inc(x_2);
x_75 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_39, x_2, x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_76 = lean_nat_add(x_67, x_52);
lean_dec(x_67);
lean_inc(x_60);
x_77 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_77, 0, x_2);
lean_ctor_set(x_77, 1, x_60);
lean_ctor_set(x_77, 2, x_74);
x_78 = lean_array_uset(x_68, x_73, x_77);
x_79 = lean_unsigned_to_nat(2u);
x_80 = lean_nat_shiftl(x_76, x_79);
x_81 = lean_unsigned_to_nat(3u);
x_82 = lean_nat_div(x_80, x_81);
lean_dec(x_80);
x_83 = lean_array_get_size(x_78);
x_84 = lean_nat_dec_le(x_82, x_83);
lean_dec(x_83);
lean_dec(x_82);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_alloc_closure((void*)(l_Lean_ExprStructEq_hash___boxed), 1, 0);
x_86 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_85, x_78);
lean_ctor_set(x_64, 1, x_86);
lean_ctor_set(x_64, 0, x_76);
x_10 = x_65;
x_11 = x_63;
x_12 = x_60;
x_13 = x_69;
x_14 = x_64;
goto block_31;
}
else
{
lean_ctor_set(x_64, 1, x_78);
lean_ctor_set(x_64, 0, x_76);
x_10 = x_65;
x_11 = x_63;
x_12 = x_60;
x_13 = x_69;
x_14 = x_64;
goto block_31;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_box(0);
x_88 = lean_array_uset(x_68, x_73, x_87);
lean_inc(x_60);
x_89 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_39, x_2, x_60, x_74);
x_90 = lean_array_uset(x_88, x_73, x_89);
lean_ctor_set(x_64, 1, x_90);
x_10 = x_65;
x_11 = x_63;
x_12 = x_60;
x_13 = x_69;
x_14 = x_64;
goto block_31;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; size_t x_95; size_t x_96; size_t x_97; lean_object* x_98; uint8_t x_99; 
x_91 = lean_ctor_get(x_64, 0);
x_92 = lean_ctor_get(x_64, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_64);
x_93 = lean_ctor_get(x_63, 0);
lean_inc(x_93);
x_94 = lean_array_get_size(x_92);
x_95 = lean_usize_of_nat(x_94);
lean_dec(x_94);
x_96 = lean_usize_sub(x_95, x_53);
x_97 = lean_usize_land(x_50, x_96);
x_98 = lean_array_uget(x_92, x_97);
lean_inc(x_98);
lean_inc(x_2);
x_99 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_39, x_2, x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_100 = lean_nat_add(x_91, x_52);
lean_dec(x_91);
lean_inc(x_60);
x_101 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_101, 0, x_2);
lean_ctor_set(x_101, 1, x_60);
lean_ctor_set(x_101, 2, x_98);
x_102 = lean_array_uset(x_92, x_97, x_101);
x_103 = lean_unsigned_to_nat(2u);
x_104 = lean_nat_shiftl(x_100, x_103);
x_105 = lean_unsigned_to_nat(3u);
x_106 = lean_nat_div(x_104, x_105);
lean_dec(x_104);
x_107 = lean_array_get_size(x_102);
x_108 = lean_nat_dec_le(x_106, x_107);
lean_dec(x_107);
lean_dec(x_106);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_alloc_closure((void*)(l_Lean_ExprStructEq_hash___boxed), 1, 0);
x_110 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_109, x_102);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_100);
lean_ctor_set(x_111, 1, x_110);
x_10 = x_65;
x_11 = x_63;
x_12 = x_60;
x_13 = x_93;
x_14 = x_111;
goto block_31;
}
else
{
lean_object* x_112; 
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_100);
lean_ctor_set(x_112, 1, x_102);
x_10 = x_65;
x_11 = x_63;
x_12 = x_60;
x_13 = x_93;
x_14 = x_112;
goto block_31;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_113 = lean_box(0);
x_114 = lean_array_uset(x_92, x_97, x_113);
lean_inc(x_60);
x_115 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_39, x_2, x_60, x_98);
x_116 = lean_array_uset(x_114, x_97, x_115);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_91);
lean_ctor_set(x_117, 1, x_116);
x_10 = x_65;
x_11 = x_63;
x_12 = x_60;
x_13 = x_93;
x_14 = x_117;
goto block_31;
}
}
}
else
{
lean_dec(x_4);
lean_dec(x_2);
return x_59;
}
}
else
{
lean_object* x_118; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_118 = lean_ctor_get(x_57, 0);
lean_inc(x_118);
lean_dec(x_57);
lean_ctor_set(x_32, 0, x_118);
return x_32;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint64_t x_123; lean_object* x_124; uint64_t x_125; uint64_t x_126; uint64_t x_127; lean_object* x_128; uint64_t x_129; uint64_t x_130; uint64_t x_131; size_t x_132; size_t x_133; lean_object* x_134; size_t x_135; size_t x_136; size_t x_137; lean_object* x_138; lean_object* x_139; 
x_119 = lean_ctor_get(x_32, 1);
lean_inc(x_119);
lean_dec(x_32);
x_120 = lean_ctor_get(x_34, 1);
lean_inc(x_120);
lean_dec(x_34);
x_121 = l_Lean_ExprStructEq_instBEq;
x_122 = lean_array_get_size(x_120);
x_123 = l_Lean_Expr_hash(x_2);
x_124 = lean_unsigned_to_nat(32u);
x_125 = lean_uint64_of_nat(x_124);
x_126 = lean_uint64_shift_right(x_123, x_125);
x_127 = lean_uint64_xor(x_123, x_126);
x_128 = lean_unsigned_to_nat(16u);
x_129 = lean_uint64_of_nat(x_128);
x_130 = lean_uint64_shift_right(x_127, x_129);
x_131 = lean_uint64_xor(x_127, x_130);
x_132 = lean_uint64_to_usize(x_131);
x_133 = lean_usize_of_nat(x_122);
lean_dec(x_122);
x_134 = lean_unsigned_to_nat(1u);
x_135 = lean_usize_of_nat(x_134);
x_136 = lean_usize_sub(x_133, x_135);
x_137 = lean_usize_land(x_132, x_136);
x_138 = lean_array_uget(x_120, x_137);
lean_dec(x_120);
lean_inc(x_2);
x_139 = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(x_121, x_2, x_138);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_box(x_3);
lean_inc(x_4);
lean_inc(x_2);
x_141 = lean_apply_8(x_1, x_2, x_140, x_4, x_5, x_6, x_7, x_8, x_119);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; size_t x_153; size_t x_154; size_t x_155; lean_object* x_156; uint8_t x_157; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_st_ref_take(x_4, x_143);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
x_147 = lean_ctor_get(x_144, 1);
lean_inc(x_147);
lean_dec(x_144);
x_148 = lean_ctor_get(x_146, 0);
lean_inc(x_148);
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
x_151 = lean_ctor_get(x_145, 0);
lean_inc(x_151);
x_152 = lean_array_get_size(x_149);
x_153 = lean_usize_of_nat(x_152);
lean_dec(x_152);
x_154 = lean_usize_sub(x_153, x_135);
x_155 = lean_usize_land(x_132, x_154);
x_156 = lean_array_uget(x_149, x_155);
lean_inc(x_156);
lean_inc(x_2);
x_157 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_121, x_2, x_156);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_158 = lean_nat_add(x_148, x_134);
lean_dec(x_148);
lean_inc(x_142);
x_159 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_159, 0, x_2);
lean_ctor_set(x_159, 1, x_142);
lean_ctor_set(x_159, 2, x_156);
x_160 = lean_array_uset(x_149, x_155, x_159);
x_161 = lean_unsigned_to_nat(2u);
x_162 = lean_nat_shiftl(x_158, x_161);
x_163 = lean_unsigned_to_nat(3u);
x_164 = lean_nat_div(x_162, x_163);
lean_dec(x_162);
x_165 = lean_array_get_size(x_160);
x_166 = lean_nat_dec_le(x_164, x_165);
lean_dec(x_165);
lean_dec(x_164);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_alloc_closure((void*)(l_Lean_ExprStructEq_hash___boxed), 1, 0);
x_168 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_167, x_160);
if (lean_is_scalar(x_150)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_150;
}
lean_ctor_set(x_169, 0, x_158);
lean_ctor_set(x_169, 1, x_168);
x_10 = x_147;
x_11 = x_145;
x_12 = x_142;
x_13 = x_151;
x_14 = x_169;
goto block_31;
}
else
{
lean_object* x_170; 
if (lean_is_scalar(x_150)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_150;
}
lean_ctor_set(x_170, 0, x_158);
lean_ctor_set(x_170, 1, x_160);
x_10 = x_147;
x_11 = x_145;
x_12 = x_142;
x_13 = x_151;
x_14 = x_170;
goto block_31;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_171 = lean_box(0);
x_172 = lean_array_uset(x_149, x_155, x_171);
lean_inc(x_142);
x_173 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_121, x_2, x_142, x_156);
x_174 = lean_array_uset(x_172, x_155, x_173);
if (lean_is_scalar(x_150)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_150;
}
lean_ctor_set(x_175, 0, x_148);
lean_ctor_set(x_175, 1, x_174);
x_10 = x_147;
x_11 = x_145;
x_12 = x_142;
x_13 = x_151;
x_14 = x_175;
goto block_31;
}
}
else
{
lean_dec(x_4);
lean_dec(x_2);
return x_141;
}
}
else
{
lean_object* x_176; lean_object* x_177; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_176 = lean_ctor_get(x_139, 0);
lean_inc(x_176);
lean_dec(x_139);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_119);
return x_177;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Meta_Closure_visitExpr(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_st_ref_take(x_2, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_mk_string_unchecked("u", 1, 1);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_ctor_get(x_5, 3);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_name_append_index_after(x_11, x_12);
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_8, 2);
lean_inc(x_16);
lean_inc(x_13);
x_17 = lean_array_push(x_16, x_13);
x_18 = lean_ctor_get(x_8, 3);
lean_inc(x_18);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_18, x_19);
lean_dec(x_18);
x_21 = lean_ctor_get(x_8, 4);
lean_inc(x_21);
x_22 = lean_array_push(x_21, x_1);
x_23 = lean_ctor_get(x_8, 5);
lean_inc(x_23);
x_24 = lean_ctor_get(x_8, 6);
lean_inc(x_24);
x_25 = lean_ctor_get(x_8, 7);
lean_inc(x_25);
x_26 = lean_ctor_get(x_8, 8);
lean_inc(x_26);
x_27 = lean_ctor_get(x_8, 9);
lean_inc(x_27);
x_28 = lean_ctor_get(x_8, 10);
lean_inc(x_28);
x_29 = lean_ctor_get(x_8, 11);
lean_inc(x_29);
lean_dec(x_8);
x_30 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_30, 0, x_14);
lean_ctor_set(x_30, 1, x_15);
lean_ctor_set(x_30, 2, x_17);
lean_ctor_set(x_30, 3, x_20);
lean_ctor_set(x_30, 4, x_22);
lean_ctor_set(x_30, 5, x_23);
lean_ctor_set(x_30, 6, x_24);
lean_ctor_set(x_30, 7, x_25);
lean_ctor_set(x_30, 8, x_26);
lean_ctor_set(x_30, 9, x_27);
lean_ctor_set(x_30, 10, x_28);
lean_ctor_set(x_30, 11, x_29);
x_31 = lean_st_ref_set(x_2, x_30, x_9);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = l_Lean_Level_param___override(x_13);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = l_Lean_Level_param___override(x_13);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Closure_mkNewLevelParam___redArg(x_1, x_3, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Closure_mkNewLevelParam___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_Closure_mkNewLevelParam(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectLevelAux_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_level_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectLevelAux_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectLevelAux_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_level_eq(x_5, x_1);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_Level_hash(x_4);
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
x_29 = l_Lean_Level_hash(x_25);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2_spec__2_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2_spec__2_spec__2___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2___redArg(lean_object* x_1) {
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
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2_spec__2___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectLevelAux_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = lean_level_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectLevelAux_spec__5___redArg(x_1, x_2, x_7);
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
x_13 = lean_level_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectLevelAux_spec__5___redArg(x_1, x_2, x_12);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectLevelAux_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectLevelAux_spec__5___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_3);
return x_22;
}
case 1:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_132; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_132 = l_Lean_Level_hasMVar(x_23);
if (x_132 == 0)
{
uint8_t x_133; 
x_133 = l_Lean_Level_hasParam(x_23);
if (x_133 == 0)
{
lean_inc(x_23);
x_24 = x_23;
x_25 = x_3;
goto block_32;
}
else
{
goto block_131;
}
}
else
{
goto block_131;
}
block_32:
{
size_t x_26; size_t x_27; uint8_t x_28; 
x_26 = lean_ptr_addr(x_23);
lean_dec(x_23);
x_27 = lean_ptr_addr(x_24);
x_28 = lean_usize_dec_eq(x_26, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_1);
x_29 = l_Lean_Level_succ___override(x_24);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
else
{
lean_object* x_31; 
lean_dec(x_24);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_25);
return x_31;
}
}
block_51:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_35, 3);
lean_inc(x_39);
x_40 = lean_ctor_get(x_35, 4);
lean_inc(x_40);
x_41 = lean_ctor_get(x_35, 5);
lean_inc(x_41);
x_42 = lean_ctor_get(x_35, 6);
lean_inc(x_42);
x_43 = lean_ctor_get(x_35, 7);
lean_inc(x_43);
x_44 = lean_ctor_get(x_35, 8);
lean_inc(x_44);
x_45 = lean_ctor_get(x_35, 9);
lean_inc(x_45);
x_46 = lean_ctor_get(x_35, 10);
lean_inc(x_46);
x_47 = lean_ctor_get(x_35, 11);
lean_inc(x_47);
lean_dec(x_35);
x_48 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_48, 0, x_36);
lean_ctor_set(x_48, 1, x_37);
lean_ctor_set(x_48, 2, x_38);
lean_ctor_set(x_48, 3, x_39);
lean_ctor_set(x_48, 4, x_40);
lean_ctor_set(x_48, 5, x_41);
lean_ctor_set(x_48, 6, x_42);
lean_ctor_set(x_48, 7, x_43);
lean_ctor_set(x_48, 8, x_44);
lean_ctor_set(x_48, 9, x_45);
lean_ctor_set(x_48, 10, x_46);
lean_ctor_set(x_48, 11, x_47);
x_49 = lean_st_ref_set(x_2, x_48, x_34);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_24 = x_33;
x_25 = x_50;
goto block_32;
}
block_131:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint64_t x_58; lean_object* x_59; uint64_t x_60; uint64_t x_61; uint64_t x_62; lean_object* x_63; uint64_t x_64; uint64_t x_65; uint64_t x_66; size_t x_67; size_t x_68; lean_object* x_69; size_t x_70; size_t x_71; size_t x_72; lean_object* x_73; lean_object* x_74; 
x_52 = lean_st_ref_get(x_2, x_3);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_array_get_size(x_56);
x_58 = l_Lean_Level_hash(x_23);
x_59 = lean_unsigned_to_nat(32u);
x_60 = lean_uint64_of_nat(x_59);
x_61 = lean_uint64_shift_right(x_58, x_60);
x_62 = lean_uint64_xor(x_58, x_61);
x_63 = lean_unsigned_to_nat(16u);
x_64 = lean_uint64_of_nat(x_63);
x_65 = lean_uint64_shift_right(x_62, x_64);
x_66 = lean_uint64_xor(x_62, x_65);
x_67 = lean_uint64_to_usize(x_66);
x_68 = lean_usize_of_nat(x_57);
lean_dec(x_57);
x_69 = lean_unsigned_to_nat(1u);
x_70 = lean_usize_of_nat(x_69);
x_71 = lean_usize_sub(x_68, x_70);
x_72 = lean_usize_land(x_67, x_71);
x_73 = lean_array_uget(x_56, x_72);
lean_dec(x_56);
x_74 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectLevelAux_spec__0___redArg(x_23, x_73);
lean_dec(x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
lean_inc(x_23);
x_75 = l_Lean_Meta_Closure_collectLevelAux___redArg(x_23, x_2, x_55);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_st_ref_take(x_2, x_77);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
x_82 = !lean_is_exclusive(x_80);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; size_t x_86; size_t x_87; size_t x_88; lean_object* x_89; uint8_t x_90; 
x_83 = lean_ctor_get(x_80, 0);
x_84 = lean_ctor_get(x_80, 1);
x_85 = lean_array_get_size(x_84);
x_86 = lean_usize_of_nat(x_85);
lean_dec(x_85);
x_87 = lean_usize_sub(x_86, x_70);
x_88 = lean_usize_land(x_67, x_87);
x_89 = lean_array_uget(x_84, x_88);
x_90 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___redArg(x_23, x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_91 = lean_nat_add(x_83, x_69);
lean_dec(x_83);
lean_inc(x_76);
lean_inc(x_23);
x_92 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_92, 0, x_23);
lean_ctor_set(x_92, 1, x_76);
lean_ctor_set(x_92, 2, x_89);
x_93 = lean_array_uset(x_84, x_88, x_92);
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
lean_object* x_100; 
x_100 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2___redArg(x_93);
lean_ctor_set(x_80, 1, x_100);
lean_ctor_set(x_80, 0, x_91);
x_33 = x_76;
x_34 = x_81;
x_35 = x_79;
x_36 = x_80;
goto block_51;
}
else
{
lean_ctor_set(x_80, 1, x_93);
lean_ctor_set(x_80, 0, x_91);
x_33 = x_76;
x_34 = x_81;
x_35 = x_79;
x_36 = x_80;
goto block_51;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_box(0);
x_102 = lean_array_uset(x_84, x_88, x_101);
lean_inc(x_76);
lean_inc(x_23);
x_103 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectLevelAux_spec__5___redArg(x_23, x_76, x_89);
x_104 = lean_array_uset(x_102, x_88, x_103);
lean_ctor_set(x_80, 1, x_104);
x_33 = x_76;
x_34 = x_81;
x_35 = x_79;
x_36 = x_80;
goto block_51;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; size_t x_108; size_t x_109; size_t x_110; lean_object* x_111; uint8_t x_112; 
x_105 = lean_ctor_get(x_80, 0);
x_106 = lean_ctor_get(x_80, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_80);
x_107 = lean_array_get_size(x_106);
x_108 = lean_usize_of_nat(x_107);
lean_dec(x_107);
x_109 = lean_usize_sub(x_108, x_70);
x_110 = lean_usize_land(x_67, x_109);
x_111 = lean_array_uget(x_106, x_110);
x_112 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___redArg(x_23, x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_113 = lean_nat_add(x_105, x_69);
lean_dec(x_105);
lean_inc(x_76);
lean_inc(x_23);
x_114 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_114, 0, x_23);
lean_ctor_set(x_114, 1, x_76);
lean_ctor_set(x_114, 2, x_111);
x_115 = lean_array_uset(x_106, x_110, x_114);
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
x_122 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2___redArg(x_115);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_113);
lean_ctor_set(x_123, 1, x_122);
x_33 = x_76;
x_34 = x_81;
x_35 = x_79;
x_36 = x_123;
goto block_51;
}
else
{
lean_object* x_124; 
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_113);
lean_ctor_set(x_124, 1, x_115);
x_33 = x_76;
x_34 = x_81;
x_35 = x_79;
x_36 = x_124;
goto block_51;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_125 = lean_box(0);
x_126 = lean_array_uset(x_106, x_110, x_125);
lean_inc(x_76);
lean_inc(x_23);
x_127 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectLevelAux_spec__5___redArg(x_23, x_76, x_111);
x_128 = lean_array_uset(x_126, x_110, x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_105);
lean_ctor_set(x_129, 1, x_128);
x_33 = x_76;
x_34 = x_81;
x_35 = x_79;
x_36 = x_129;
goto block_51;
}
}
}
else
{
lean_object* x_130; 
x_130 = lean_ctor_get(x_74, 0);
lean_inc(x_130);
lean_dec(x_74);
x_24 = x_130;
x_25 = x_55;
goto block_32;
}
}
}
case 2:
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_166; lean_object* x_167; lean_object* x_248; lean_object* x_249; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_352; 
x_134 = lean_ctor_get(x_1, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_1, 1);
lean_inc(x_135);
x_352 = l_Lean_Level_hasMVar(x_134);
if (x_352 == 0)
{
uint8_t x_353; 
x_353 = l_Lean_Level_hasParam(x_134);
if (x_353 == 0)
{
lean_inc(x_134);
x_248 = x_134;
x_249 = x_3;
goto block_252;
}
else
{
goto block_351;
}
}
else
{
goto block_351;
}
block_145:
{
size_t x_139; size_t x_140; uint8_t x_141; 
x_139 = lean_ptr_addr(x_134);
lean_dec(x_134);
x_140 = lean_ptr_addr(x_136);
x_141 = lean_usize_dec_eq(x_139, x_140);
if (x_141 == 0)
{
lean_dec(x_135);
x_13 = x_138;
x_14 = x_137;
x_15 = x_136;
x_16 = x_141;
goto block_21;
}
else
{
size_t x_142; size_t x_143; uint8_t x_144; 
x_142 = lean_ptr_addr(x_135);
lean_dec(x_135);
x_143 = lean_ptr_addr(x_137);
x_144 = lean_usize_dec_eq(x_142, x_143);
x_13 = x_138;
x_14 = x_137;
x_15 = x_136;
x_16 = x_144;
goto block_21;
}
}
block_165:
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_151 = lean_ctor_get(x_146, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_146, 2);
lean_inc(x_152);
x_153 = lean_ctor_get(x_146, 3);
lean_inc(x_153);
x_154 = lean_ctor_get(x_146, 4);
lean_inc(x_154);
x_155 = lean_ctor_get(x_146, 5);
lean_inc(x_155);
x_156 = lean_ctor_get(x_146, 6);
lean_inc(x_156);
x_157 = lean_ctor_get(x_146, 7);
lean_inc(x_157);
x_158 = lean_ctor_get(x_146, 8);
lean_inc(x_158);
x_159 = lean_ctor_get(x_146, 9);
lean_inc(x_159);
x_160 = lean_ctor_get(x_146, 10);
lean_inc(x_160);
x_161 = lean_ctor_get(x_146, 11);
lean_inc(x_161);
lean_dec(x_146);
x_162 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_162, 0, x_150);
lean_ctor_set(x_162, 1, x_151);
lean_ctor_set(x_162, 2, x_152);
lean_ctor_set(x_162, 3, x_153);
lean_ctor_set(x_162, 4, x_154);
lean_ctor_set(x_162, 5, x_155);
lean_ctor_set(x_162, 6, x_156);
lean_ctor_set(x_162, 7, x_157);
lean_ctor_set(x_162, 8, x_158);
lean_ctor_set(x_162, 9, x_159);
lean_ctor_set(x_162, 10, x_160);
lean_ctor_set(x_162, 11, x_161);
x_163 = lean_st_ref_set(x_2, x_162, x_147);
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
lean_dec(x_163);
x_136 = x_149;
x_137 = x_148;
x_138 = x_164;
goto block_145;
}
block_247:
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint64_t x_174; lean_object* x_175; uint64_t x_176; uint64_t x_177; uint64_t x_178; lean_object* x_179; uint64_t x_180; uint64_t x_181; uint64_t x_182; size_t x_183; size_t x_184; lean_object* x_185; size_t x_186; size_t x_187; size_t x_188; lean_object* x_189; lean_object* x_190; 
x_168 = lean_st_ref_get(x_2, x_166);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
lean_dec(x_169);
x_171 = lean_ctor_get(x_168, 1);
lean_inc(x_171);
lean_dec(x_168);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_array_get_size(x_172);
x_174 = l_Lean_Level_hash(x_135);
x_175 = lean_unsigned_to_nat(32u);
x_176 = lean_uint64_of_nat(x_175);
x_177 = lean_uint64_shift_right(x_174, x_176);
x_178 = lean_uint64_xor(x_174, x_177);
x_179 = lean_unsigned_to_nat(16u);
x_180 = lean_uint64_of_nat(x_179);
x_181 = lean_uint64_shift_right(x_178, x_180);
x_182 = lean_uint64_xor(x_178, x_181);
x_183 = lean_uint64_to_usize(x_182);
x_184 = lean_usize_of_nat(x_173);
lean_dec(x_173);
x_185 = lean_unsigned_to_nat(1u);
x_186 = lean_usize_of_nat(x_185);
x_187 = lean_usize_sub(x_184, x_186);
x_188 = lean_usize_land(x_183, x_187);
x_189 = lean_array_uget(x_172, x_188);
lean_dec(x_172);
x_190 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectLevelAux_spec__0___redArg(x_135, x_189);
lean_dec(x_189);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; 
lean_inc(x_135);
x_191 = l_Lean_Meta_Closure_collectLevelAux___redArg(x_135, x_2, x_171);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
x_194 = lean_st_ref_take(x_2, x_193);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_194, 1);
lean_inc(x_197);
lean_dec(x_194);
x_198 = !lean_is_exclusive(x_196);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; size_t x_202; size_t x_203; size_t x_204; lean_object* x_205; uint8_t x_206; 
x_199 = lean_ctor_get(x_196, 0);
x_200 = lean_ctor_get(x_196, 1);
x_201 = lean_array_get_size(x_200);
x_202 = lean_usize_of_nat(x_201);
lean_dec(x_201);
x_203 = lean_usize_sub(x_202, x_186);
x_204 = lean_usize_land(x_183, x_203);
x_205 = lean_array_uget(x_200, x_204);
x_206 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___redArg(x_135, x_205);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; 
x_207 = lean_nat_add(x_199, x_185);
lean_dec(x_199);
lean_inc(x_192);
lean_inc(x_135);
x_208 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_208, 0, x_135);
lean_ctor_set(x_208, 1, x_192);
lean_ctor_set(x_208, 2, x_205);
x_209 = lean_array_uset(x_200, x_204, x_208);
x_210 = lean_unsigned_to_nat(2u);
x_211 = lean_nat_shiftl(x_207, x_210);
x_212 = lean_unsigned_to_nat(3u);
x_213 = lean_nat_div(x_211, x_212);
lean_dec(x_211);
x_214 = lean_array_get_size(x_209);
x_215 = lean_nat_dec_le(x_213, x_214);
lean_dec(x_214);
lean_dec(x_213);
if (x_215 == 0)
{
lean_object* x_216; 
x_216 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2___redArg(x_209);
lean_ctor_set(x_196, 1, x_216);
lean_ctor_set(x_196, 0, x_207);
x_146 = x_195;
x_147 = x_197;
x_148 = x_192;
x_149 = x_167;
x_150 = x_196;
goto block_165;
}
else
{
lean_ctor_set(x_196, 1, x_209);
lean_ctor_set(x_196, 0, x_207);
x_146 = x_195;
x_147 = x_197;
x_148 = x_192;
x_149 = x_167;
x_150 = x_196;
goto block_165;
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_217 = lean_box(0);
x_218 = lean_array_uset(x_200, x_204, x_217);
lean_inc(x_192);
lean_inc(x_135);
x_219 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectLevelAux_spec__5___redArg(x_135, x_192, x_205);
x_220 = lean_array_uset(x_218, x_204, x_219);
lean_ctor_set(x_196, 1, x_220);
x_146 = x_195;
x_147 = x_197;
x_148 = x_192;
x_149 = x_167;
x_150 = x_196;
goto block_165;
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; size_t x_224; size_t x_225; size_t x_226; lean_object* x_227; uint8_t x_228; 
x_221 = lean_ctor_get(x_196, 0);
x_222 = lean_ctor_get(x_196, 1);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_196);
x_223 = lean_array_get_size(x_222);
x_224 = lean_usize_of_nat(x_223);
lean_dec(x_223);
x_225 = lean_usize_sub(x_224, x_186);
x_226 = lean_usize_land(x_183, x_225);
x_227 = lean_array_uget(x_222, x_226);
x_228 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___redArg(x_135, x_227);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; 
x_229 = lean_nat_add(x_221, x_185);
lean_dec(x_221);
lean_inc(x_192);
lean_inc(x_135);
x_230 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_230, 0, x_135);
lean_ctor_set(x_230, 1, x_192);
lean_ctor_set(x_230, 2, x_227);
x_231 = lean_array_uset(x_222, x_226, x_230);
x_232 = lean_unsigned_to_nat(2u);
x_233 = lean_nat_shiftl(x_229, x_232);
x_234 = lean_unsigned_to_nat(3u);
x_235 = lean_nat_div(x_233, x_234);
lean_dec(x_233);
x_236 = lean_array_get_size(x_231);
x_237 = lean_nat_dec_le(x_235, x_236);
lean_dec(x_236);
lean_dec(x_235);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; 
x_238 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2___redArg(x_231);
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_229);
lean_ctor_set(x_239, 1, x_238);
x_146 = x_195;
x_147 = x_197;
x_148 = x_192;
x_149 = x_167;
x_150 = x_239;
goto block_165;
}
else
{
lean_object* x_240; 
x_240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_240, 0, x_229);
lean_ctor_set(x_240, 1, x_231);
x_146 = x_195;
x_147 = x_197;
x_148 = x_192;
x_149 = x_167;
x_150 = x_240;
goto block_165;
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_241 = lean_box(0);
x_242 = lean_array_uset(x_222, x_226, x_241);
lean_inc(x_192);
lean_inc(x_135);
x_243 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectLevelAux_spec__5___redArg(x_135, x_192, x_227);
x_244 = lean_array_uset(x_242, x_226, x_243);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_221);
lean_ctor_set(x_245, 1, x_244);
x_146 = x_195;
x_147 = x_197;
x_148 = x_192;
x_149 = x_167;
x_150 = x_245;
goto block_165;
}
}
}
else
{
lean_object* x_246; 
x_246 = lean_ctor_get(x_190, 0);
lean_inc(x_246);
lean_dec(x_190);
x_136 = x_167;
x_137 = x_246;
x_138 = x_171;
goto block_145;
}
}
block_252:
{
uint8_t x_250; 
x_250 = l_Lean_Level_hasMVar(x_135);
if (x_250 == 0)
{
uint8_t x_251; 
x_251 = l_Lean_Level_hasParam(x_135);
if (x_251 == 0)
{
lean_inc(x_135);
x_136 = x_248;
x_137 = x_135;
x_138 = x_249;
goto block_145;
}
else
{
x_166 = x_249;
x_167 = x_248;
goto block_247;
}
}
else
{
x_166 = x_249;
x_167 = x_248;
goto block_247;
}
}
block_271:
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_257 = lean_ctor_get(x_253, 1);
lean_inc(x_257);
x_258 = lean_ctor_get(x_253, 2);
lean_inc(x_258);
x_259 = lean_ctor_get(x_253, 3);
lean_inc(x_259);
x_260 = lean_ctor_get(x_253, 4);
lean_inc(x_260);
x_261 = lean_ctor_get(x_253, 5);
lean_inc(x_261);
x_262 = lean_ctor_get(x_253, 6);
lean_inc(x_262);
x_263 = lean_ctor_get(x_253, 7);
lean_inc(x_263);
x_264 = lean_ctor_get(x_253, 8);
lean_inc(x_264);
x_265 = lean_ctor_get(x_253, 9);
lean_inc(x_265);
x_266 = lean_ctor_get(x_253, 10);
lean_inc(x_266);
x_267 = lean_ctor_get(x_253, 11);
lean_inc(x_267);
lean_dec(x_253);
x_268 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_268, 0, x_256);
lean_ctor_set(x_268, 1, x_257);
lean_ctor_set(x_268, 2, x_258);
lean_ctor_set(x_268, 3, x_259);
lean_ctor_set(x_268, 4, x_260);
lean_ctor_set(x_268, 5, x_261);
lean_ctor_set(x_268, 6, x_262);
lean_ctor_set(x_268, 7, x_263);
lean_ctor_set(x_268, 8, x_264);
lean_ctor_set(x_268, 9, x_265);
lean_ctor_set(x_268, 10, x_266);
lean_ctor_set(x_268, 11, x_267);
x_269 = lean_st_ref_set(x_2, x_268, x_255);
x_270 = lean_ctor_get(x_269, 1);
lean_inc(x_270);
lean_dec(x_269);
x_248 = x_254;
x_249 = x_270;
goto block_252;
}
block_351:
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; uint64_t x_278; lean_object* x_279; uint64_t x_280; uint64_t x_281; uint64_t x_282; lean_object* x_283; uint64_t x_284; uint64_t x_285; uint64_t x_286; size_t x_287; size_t x_288; lean_object* x_289; size_t x_290; size_t x_291; size_t x_292; lean_object* x_293; lean_object* x_294; 
x_272 = lean_st_ref_get(x_2, x_3);
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
lean_dec(x_273);
x_275 = lean_ctor_get(x_272, 1);
lean_inc(x_275);
lean_dec(x_272);
x_276 = lean_ctor_get(x_274, 1);
lean_inc(x_276);
lean_dec(x_274);
x_277 = lean_array_get_size(x_276);
x_278 = l_Lean_Level_hash(x_134);
x_279 = lean_unsigned_to_nat(32u);
x_280 = lean_uint64_of_nat(x_279);
x_281 = lean_uint64_shift_right(x_278, x_280);
x_282 = lean_uint64_xor(x_278, x_281);
x_283 = lean_unsigned_to_nat(16u);
x_284 = lean_uint64_of_nat(x_283);
x_285 = lean_uint64_shift_right(x_282, x_284);
x_286 = lean_uint64_xor(x_282, x_285);
x_287 = lean_uint64_to_usize(x_286);
x_288 = lean_usize_of_nat(x_277);
lean_dec(x_277);
x_289 = lean_unsigned_to_nat(1u);
x_290 = lean_usize_of_nat(x_289);
x_291 = lean_usize_sub(x_288, x_290);
x_292 = lean_usize_land(x_287, x_291);
x_293 = lean_array_uget(x_276, x_292);
lean_dec(x_276);
x_294 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectLevelAux_spec__0___redArg(x_134, x_293);
lean_dec(x_293);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; 
lean_inc(x_134);
x_295 = l_Lean_Meta_Closure_collectLevelAux___redArg(x_134, x_2, x_275);
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_295, 1);
lean_inc(x_297);
lean_dec(x_295);
x_298 = lean_st_ref_take(x_2, x_297);
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_298, 1);
lean_inc(x_301);
lean_dec(x_298);
x_302 = !lean_is_exclusive(x_300);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; size_t x_306; size_t x_307; size_t x_308; lean_object* x_309; uint8_t x_310; 
x_303 = lean_ctor_get(x_300, 0);
x_304 = lean_ctor_get(x_300, 1);
x_305 = lean_array_get_size(x_304);
x_306 = lean_usize_of_nat(x_305);
lean_dec(x_305);
x_307 = lean_usize_sub(x_306, x_290);
x_308 = lean_usize_land(x_287, x_307);
x_309 = lean_array_uget(x_304, x_308);
x_310 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___redArg(x_134, x_309);
if (x_310 == 0)
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; uint8_t x_319; 
x_311 = lean_nat_add(x_303, x_289);
lean_dec(x_303);
lean_inc(x_296);
lean_inc(x_134);
x_312 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_312, 0, x_134);
lean_ctor_set(x_312, 1, x_296);
lean_ctor_set(x_312, 2, x_309);
x_313 = lean_array_uset(x_304, x_308, x_312);
x_314 = lean_unsigned_to_nat(2u);
x_315 = lean_nat_shiftl(x_311, x_314);
x_316 = lean_unsigned_to_nat(3u);
x_317 = lean_nat_div(x_315, x_316);
lean_dec(x_315);
x_318 = lean_array_get_size(x_313);
x_319 = lean_nat_dec_le(x_317, x_318);
lean_dec(x_318);
lean_dec(x_317);
if (x_319 == 0)
{
lean_object* x_320; 
x_320 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2___redArg(x_313);
lean_ctor_set(x_300, 1, x_320);
lean_ctor_set(x_300, 0, x_311);
x_253 = x_299;
x_254 = x_296;
x_255 = x_301;
x_256 = x_300;
goto block_271;
}
else
{
lean_ctor_set(x_300, 1, x_313);
lean_ctor_set(x_300, 0, x_311);
x_253 = x_299;
x_254 = x_296;
x_255 = x_301;
x_256 = x_300;
goto block_271;
}
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_321 = lean_box(0);
x_322 = lean_array_uset(x_304, x_308, x_321);
lean_inc(x_296);
lean_inc(x_134);
x_323 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectLevelAux_spec__5___redArg(x_134, x_296, x_309);
x_324 = lean_array_uset(x_322, x_308, x_323);
lean_ctor_set(x_300, 1, x_324);
x_253 = x_299;
x_254 = x_296;
x_255 = x_301;
x_256 = x_300;
goto block_271;
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; size_t x_328; size_t x_329; size_t x_330; lean_object* x_331; uint8_t x_332; 
x_325 = lean_ctor_get(x_300, 0);
x_326 = lean_ctor_get(x_300, 1);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_300);
x_327 = lean_array_get_size(x_326);
x_328 = lean_usize_of_nat(x_327);
lean_dec(x_327);
x_329 = lean_usize_sub(x_328, x_290);
x_330 = lean_usize_land(x_287, x_329);
x_331 = lean_array_uget(x_326, x_330);
x_332 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___redArg(x_134, x_331);
if (x_332 == 0)
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; uint8_t x_341; 
x_333 = lean_nat_add(x_325, x_289);
lean_dec(x_325);
lean_inc(x_296);
lean_inc(x_134);
x_334 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_334, 0, x_134);
lean_ctor_set(x_334, 1, x_296);
lean_ctor_set(x_334, 2, x_331);
x_335 = lean_array_uset(x_326, x_330, x_334);
x_336 = lean_unsigned_to_nat(2u);
x_337 = lean_nat_shiftl(x_333, x_336);
x_338 = lean_unsigned_to_nat(3u);
x_339 = lean_nat_div(x_337, x_338);
lean_dec(x_337);
x_340 = lean_array_get_size(x_335);
x_341 = lean_nat_dec_le(x_339, x_340);
lean_dec(x_340);
lean_dec(x_339);
if (x_341 == 0)
{
lean_object* x_342; lean_object* x_343; 
x_342 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2___redArg(x_335);
x_343 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_343, 0, x_333);
lean_ctor_set(x_343, 1, x_342);
x_253 = x_299;
x_254 = x_296;
x_255 = x_301;
x_256 = x_343;
goto block_271;
}
else
{
lean_object* x_344; 
x_344 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_344, 0, x_333);
lean_ctor_set(x_344, 1, x_335);
x_253 = x_299;
x_254 = x_296;
x_255 = x_301;
x_256 = x_344;
goto block_271;
}
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_345 = lean_box(0);
x_346 = lean_array_uset(x_326, x_330, x_345);
lean_inc(x_296);
lean_inc(x_134);
x_347 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectLevelAux_spec__5___redArg(x_134, x_296, x_331);
x_348 = lean_array_uset(x_346, x_330, x_347);
x_349 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_349, 0, x_325);
lean_ctor_set(x_349, 1, x_348);
x_253 = x_299;
x_254 = x_296;
x_255 = x_301;
x_256 = x_349;
goto block_271;
}
}
}
else
{
lean_object* x_350; 
x_350 = lean_ctor_get(x_294, 0);
lean_inc(x_350);
lean_dec(x_294);
x_248 = x_350;
x_249 = x_275;
goto block_252;
}
}
}
case 3:
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_386; lean_object* x_387; lean_object* x_468; lean_object* x_469; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; uint8_t x_572; 
x_354 = lean_ctor_get(x_1, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_1, 1);
lean_inc(x_355);
x_572 = l_Lean_Level_hasMVar(x_354);
if (x_572 == 0)
{
uint8_t x_573; 
x_573 = l_Lean_Level_hasParam(x_354);
if (x_573 == 0)
{
lean_inc(x_354);
x_468 = x_354;
x_469 = x_3;
goto block_472;
}
else
{
goto block_571;
}
}
else
{
goto block_571;
}
block_365:
{
size_t x_359; size_t x_360; uint8_t x_361; 
x_359 = lean_ptr_addr(x_354);
lean_dec(x_354);
x_360 = lean_ptr_addr(x_356);
x_361 = lean_usize_dec_eq(x_359, x_360);
if (x_361 == 0)
{
lean_dec(x_355);
x_4 = x_356;
x_5 = x_358;
x_6 = x_357;
x_7 = x_361;
goto block_12;
}
else
{
size_t x_362; size_t x_363; uint8_t x_364; 
x_362 = lean_ptr_addr(x_355);
lean_dec(x_355);
x_363 = lean_ptr_addr(x_357);
x_364 = lean_usize_dec_eq(x_362, x_363);
x_4 = x_356;
x_5 = x_358;
x_6 = x_357;
x_7 = x_364;
goto block_12;
}
}
block_385:
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_371 = lean_ctor_get(x_368, 1);
lean_inc(x_371);
x_372 = lean_ctor_get(x_368, 2);
lean_inc(x_372);
x_373 = lean_ctor_get(x_368, 3);
lean_inc(x_373);
x_374 = lean_ctor_get(x_368, 4);
lean_inc(x_374);
x_375 = lean_ctor_get(x_368, 5);
lean_inc(x_375);
x_376 = lean_ctor_get(x_368, 6);
lean_inc(x_376);
x_377 = lean_ctor_get(x_368, 7);
lean_inc(x_377);
x_378 = lean_ctor_get(x_368, 8);
lean_inc(x_378);
x_379 = lean_ctor_get(x_368, 9);
lean_inc(x_379);
x_380 = lean_ctor_get(x_368, 10);
lean_inc(x_380);
x_381 = lean_ctor_get(x_368, 11);
lean_inc(x_381);
lean_dec(x_368);
x_382 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_382, 0, x_370);
lean_ctor_set(x_382, 1, x_371);
lean_ctor_set(x_382, 2, x_372);
lean_ctor_set(x_382, 3, x_373);
lean_ctor_set(x_382, 4, x_374);
lean_ctor_set(x_382, 5, x_375);
lean_ctor_set(x_382, 6, x_376);
lean_ctor_set(x_382, 7, x_377);
lean_ctor_set(x_382, 8, x_378);
lean_ctor_set(x_382, 9, x_379);
lean_ctor_set(x_382, 10, x_380);
lean_ctor_set(x_382, 11, x_381);
x_383 = lean_st_ref_set(x_2, x_382, x_367);
x_384 = lean_ctor_get(x_383, 1);
lean_inc(x_384);
lean_dec(x_383);
x_356 = x_366;
x_357 = x_369;
x_358 = x_384;
goto block_365;
}
block_467:
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; uint64_t x_394; lean_object* x_395; uint64_t x_396; uint64_t x_397; uint64_t x_398; lean_object* x_399; uint64_t x_400; uint64_t x_401; uint64_t x_402; size_t x_403; size_t x_404; lean_object* x_405; size_t x_406; size_t x_407; size_t x_408; lean_object* x_409; lean_object* x_410; 
x_388 = lean_st_ref_get(x_2, x_387);
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_389, 0);
lean_inc(x_390);
lean_dec(x_389);
x_391 = lean_ctor_get(x_388, 1);
lean_inc(x_391);
lean_dec(x_388);
x_392 = lean_ctor_get(x_390, 1);
lean_inc(x_392);
lean_dec(x_390);
x_393 = lean_array_get_size(x_392);
x_394 = l_Lean_Level_hash(x_355);
x_395 = lean_unsigned_to_nat(32u);
x_396 = lean_uint64_of_nat(x_395);
x_397 = lean_uint64_shift_right(x_394, x_396);
x_398 = lean_uint64_xor(x_394, x_397);
x_399 = lean_unsigned_to_nat(16u);
x_400 = lean_uint64_of_nat(x_399);
x_401 = lean_uint64_shift_right(x_398, x_400);
x_402 = lean_uint64_xor(x_398, x_401);
x_403 = lean_uint64_to_usize(x_402);
x_404 = lean_usize_of_nat(x_393);
lean_dec(x_393);
x_405 = lean_unsigned_to_nat(1u);
x_406 = lean_usize_of_nat(x_405);
x_407 = lean_usize_sub(x_404, x_406);
x_408 = lean_usize_land(x_403, x_407);
x_409 = lean_array_uget(x_392, x_408);
lean_dec(x_392);
x_410 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectLevelAux_spec__0___redArg(x_355, x_409);
lean_dec(x_409);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; 
lean_inc(x_355);
x_411 = l_Lean_Meta_Closure_collectLevelAux___redArg(x_355, x_2, x_391);
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_411, 1);
lean_inc(x_413);
lean_dec(x_411);
x_414 = lean_st_ref_take(x_2, x_413);
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_415, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_414, 1);
lean_inc(x_417);
lean_dec(x_414);
x_418 = !lean_is_exclusive(x_416);
if (x_418 == 0)
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; size_t x_422; size_t x_423; size_t x_424; lean_object* x_425; uint8_t x_426; 
x_419 = lean_ctor_get(x_416, 0);
x_420 = lean_ctor_get(x_416, 1);
x_421 = lean_array_get_size(x_420);
x_422 = lean_usize_of_nat(x_421);
lean_dec(x_421);
x_423 = lean_usize_sub(x_422, x_406);
x_424 = lean_usize_land(x_403, x_423);
x_425 = lean_array_uget(x_420, x_424);
x_426 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___redArg(x_355, x_425);
if (x_426 == 0)
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; uint8_t x_435; 
x_427 = lean_nat_add(x_419, x_405);
lean_dec(x_419);
lean_inc(x_412);
lean_inc(x_355);
x_428 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_428, 0, x_355);
lean_ctor_set(x_428, 1, x_412);
lean_ctor_set(x_428, 2, x_425);
x_429 = lean_array_uset(x_420, x_424, x_428);
x_430 = lean_unsigned_to_nat(2u);
x_431 = lean_nat_shiftl(x_427, x_430);
x_432 = lean_unsigned_to_nat(3u);
x_433 = lean_nat_div(x_431, x_432);
lean_dec(x_431);
x_434 = lean_array_get_size(x_429);
x_435 = lean_nat_dec_le(x_433, x_434);
lean_dec(x_434);
lean_dec(x_433);
if (x_435 == 0)
{
lean_object* x_436; 
x_436 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2___redArg(x_429);
lean_ctor_set(x_416, 1, x_436);
lean_ctor_set(x_416, 0, x_427);
x_366 = x_386;
x_367 = x_417;
x_368 = x_415;
x_369 = x_412;
x_370 = x_416;
goto block_385;
}
else
{
lean_ctor_set(x_416, 1, x_429);
lean_ctor_set(x_416, 0, x_427);
x_366 = x_386;
x_367 = x_417;
x_368 = x_415;
x_369 = x_412;
x_370 = x_416;
goto block_385;
}
}
else
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; 
x_437 = lean_box(0);
x_438 = lean_array_uset(x_420, x_424, x_437);
lean_inc(x_412);
lean_inc(x_355);
x_439 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectLevelAux_spec__5___redArg(x_355, x_412, x_425);
x_440 = lean_array_uset(x_438, x_424, x_439);
lean_ctor_set(x_416, 1, x_440);
x_366 = x_386;
x_367 = x_417;
x_368 = x_415;
x_369 = x_412;
x_370 = x_416;
goto block_385;
}
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; size_t x_444; size_t x_445; size_t x_446; lean_object* x_447; uint8_t x_448; 
x_441 = lean_ctor_get(x_416, 0);
x_442 = lean_ctor_get(x_416, 1);
lean_inc(x_442);
lean_inc(x_441);
lean_dec(x_416);
x_443 = lean_array_get_size(x_442);
x_444 = lean_usize_of_nat(x_443);
lean_dec(x_443);
x_445 = lean_usize_sub(x_444, x_406);
x_446 = lean_usize_land(x_403, x_445);
x_447 = lean_array_uget(x_442, x_446);
x_448 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___redArg(x_355, x_447);
if (x_448 == 0)
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; uint8_t x_457; 
x_449 = lean_nat_add(x_441, x_405);
lean_dec(x_441);
lean_inc(x_412);
lean_inc(x_355);
x_450 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_450, 0, x_355);
lean_ctor_set(x_450, 1, x_412);
lean_ctor_set(x_450, 2, x_447);
x_451 = lean_array_uset(x_442, x_446, x_450);
x_452 = lean_unsigned_to_nat(2u);
x_453 = lean_nat_shiftl(x_449, x_452);
x_454 = lean_unsigned_to_nat(3u);
x_455 = lean_nat_div(x_453, x_454);
lean_dec(x_453);
x_456 = lean_array_get_size(x_451);
x_457 = lean_nat_dec_le(x_455, x_456);
lean_dec(x_456);
lean_dec(x_455);
if (x_457 == 0)
{
lean_object* x_458; lean_object* x_459; 
x_458 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2___redArg(x_451);
x_459 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_459, 0, x_449);
lean_ctor_set(x_459, 1, x_458);
x_366 = x_386;
x_367 = x_417;
x_368 = x_415;
x_369 = x_412;
x_370 = x_459;
goto block_385;
}
else
{
lean_object* x_460; 
x_460 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_460, 0, x_449);
lean_ctor_set(x_460, 1, x_451);
x_366 = x_386;
x_367 = x_417;
x_368 = x_415;
x_369 = x_412;
x_370 = x_460;
goto block_385;
}
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_461 = lean_box(0);
x_462 = lean_array_uset(x_442, x_446, x_461);
lean_inc(x_412);
lean_inc(x_355);
x_463 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectLevelAux_spec__5___redArg(x_355, x_412, x_447);
x_464 = lean_array_uset(x_462, x_446, x_463);
x_465 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_465, 0, x_441);
lean_ctor_set(x_465, 1, x_464);
x_366 = x_386;
x_367 = x_417;
x_368 = x_415;
x_369 = x_412;
x_370 = x_465;
goto block_385;
}
}
}
else
{
lean_object* x_466; 
x_466 = lean_ctor_get(x_410, 0);
lean_inc(x_466);
lean_dec(x_410);
x_356 = x_386;
x_357 = x_466;
x_358 = x_391;
goto block_365;
}
}
block_472:
{
uint8_t x_470; 
x_470 = l_Lean_Level_hasMVar(x_355);
if (x_470 == 0)
{
uint8_t x_471; 
x_471 = l_Lean_Level_hasParam(x_355);
if (x_471 == 0)
{
lean_inc(x_355);
x_356 = x_468;
x_357 = x_355;
x_358 = x_469;
goto block_365;
}
else
{
x_386 = x_468;
x_387 = x_469;
goto block_467;
}
}
else
{
x_386 = x_468;
x_387 = x_469;
goto block_467;
}
}
block_491:
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_477 = lean_ctor_get(x_475, 1);
lean_inc(x_477);
x_478 = lean_ctor_get(x_475, 2);
lean_inc(x_478);
x_479 = lean_ctor_get(x_475, 3);
lean_inc(x_479);
x_480 = lean_ctor_get(x_475, 4);
lean_inc(x_480);
x_481 = lean_ctor_get(x_475, 5);
lean_inc(x_481);
x_482 = lean_ctor_get(x_475, 6);
lean_inc(x_482);
x_483 = lean_ctor_get(x_475, 7);
lean_inc(x_483);
x_484 = lean_ctor_get(x_475, 8);
lean_inc(x_484);
x_485 = lean_ctor_get(x_475, 9);
lean_inc(x_485);
x_486 = lean_ctor_get(x_475, 10);
lean_inc(x_486);
x_487 = lean_ctor_get(x_475, 11);
lean_inc(x_487);
lean_dec(x_475);
x_488 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_488, 0, x_476);
lean_ctor_set(x_488, 1, x_477);
lean_ctor_set(x_488, 2, x_478);
lean_ctor_set(x_488, 3, x_479);
lean_ctor_set(x_488, 4, x_480);
lean_ctor_set(x_488, 5, x_481);
lean_ctor_set(x_488, 6, x_482);
lean_ctor_set(x_488, 7, x_483);
lean_ctor_set(x_488, 8, x_484);
lean_ctor_set(x_488, 9, x_485);
lean_ctor_set(x_488, 10, x_486);
lean_ctor_set(x_488, 11, x_487);
x_489 = lean_st_ref_set(x_2, x_488, x_473);
x_490 = lean_ctor_get(x_489, 1);
lean_inc(x_490);
lean_dec(x_489);
x_468 = x_474;
x_469 = x_490;
goto block_472;
}
block_571:
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; uint64_t x_498; lean_object* x_499; uint64_t x_500; uint64_t x_501; uint64_t x_502; lean_object* x_503; uint64_t x_504; uint64_t x_505; uint64_t x_506; size_t x_507; size_t x_508; lean_object* x_509; size_t x_510; size_t x_511; size_t x_512; lean_object* x_513; lean_object* x_514; 
x_492 = lean_st_ref_get(x_2, x_3);
x_493 = lean_ctor_get(x_492, 0);
lean_inc(x_493);
x_494 = lean_ctor_get(x_493, 0);
lean_inc(x_494);
lean_dec(x_493);
x_495 = lean_ctor_get(x_492, 1);
lean_inc(x_495);
lean_dec(x_492);
x_496 = lean_ctor_get(x_494, 1);
lean_inc(x_496);
lean_dec(x_494);
x_497 = lean_array_get_size(x_496);
x_498 = l_Lean_Level_hash(x_354);
x_499 = lean_unsigned_to_nat(32u);
x_500 = lean_uint64_of_nat(x_499);
x_501 = lean_uint64_shift_right(x_498, x_500);
x_502 = lean_uint64_xor(x_498, x_501);
x_503 = lean_unsigned_to_nat(16u);
x_504 = lean_uint64_of_nat(x_503);
x_505 = lean_uint64_shift_right(x_502, x_504);
x_506 = lean_uint64_xor(x_502, x_505);
x_507 = lean_uint64_to_usize(x_506);
x_508 = lean_usize_of_nat(x_497);
lean_dec(x_497);
x_509 = lean_unsigned_to_nat(1u);
x_510 = lean_usize_of_nat(x_509);
x_511 = lean_usize_sub(x_508, x_510);
x_512 = lean_usize_land(x_507, x_511);
x_513 = lean_array_uget(x_496, x_512);
lean_dec(x_496);
x_514 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectLevelAux_spec__0___redArg(x_354, x_513);
lean_dec(x_513);
if (lean_obj_tag(x_514) == 0)
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; uint8_t x_522; 
lean_inc(x_354);
x_515 = l_Lean_Meta_Closure_collectLevelAux___redArg(x_354, x_2, x_495);
x_516 = lean_ctor_get(x_515, 0);
lean_inc(x_516);
x_517 = lean_ctor_get(x_515, 1);
lean_inc(x_517);
lean_dec(x_515);
x_518 = lean_st_ref_take(x_2, x_517);
x_519 = lean_ctor_get(x_518, 0);
lean_inc(x_519);
x_520 = lean_ctor_get(x_519, 0);
lean_inc(x_520);
x_521 = lean_ctor_get(x_518, 1);
lean_inc(x_521);
lean_dec(x_518);
x_522 = !lean_is_exclusive(x_520);
if (x_522 == 0)
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; size_t x_526; size_t x_527; size_t x_528; lean_object* x_529; uint8_t x_530; 
x_523 = lean_ctor_get(x_520, 0);
x_524 = lean_ctor_get(x_520, 1);
x_525 = lean_array_get_size(x_524);
x_526 = lean_usize_of_nat(x_525);
lean_dec(x_525);
x_527 = lean_usize_sub(x_526, x_510);
x_528 = lean_usize_land(x_507, x_527);
x_529 = lean_array_uget(x_524, x_528);
x_530 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___redArg(x_354, x_529);
if (x_530 == 0)
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; uint8_t x_539; 
x_531 = lean_nat_add(x_523, x_509);
lean_dec(x_523);
lean_inc(x_516);
lean_inc(x_354);
x_532 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_532, 0, x_354);
lean_ctor_set(x_532, 1, x_516);
lean_ctor_set(x_532, 2, x_529);
x_533 = lean_array_uset(x_524, x_528, x_532);
x_534 = lean_unsigned_to_nat(2u);
x_535 = lean_nat_shiftl(x_531, x_534);
x_536 = lean_unsigned_to_nat(3u);
x_537 = lean_nat_div(x_535, x_536);
lean_dec(x_535);
x_538 = lean_array_get_size(x_533);
x_539 = lean_nat_dec_le(x_537, x_538);
lean_dec(x_538);
lean_dec(x_537);
if (x_539 == 0)
{
lean_object* x_540; 
x_540 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2___redArg(x_533);
lean_ctor_set(x_520, 1, x_540);
lean_ctor_set(x_520, 0, x_531);
x_473 = x_521;
x_474 = x_516;
x_475 = x_519;
x_476 = x_520;
goto block_491;
}
else
{
lean_ctor_set(x_520, 1, x_533);
lean_ctor_set(x_520, 0, x_531);
x_473 = x_521;
x_474 = x_516;
x_475 = x_519;
x_476 = x_520;
goto block_491;
}
}
else
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; 
x_541 = lean_box(0);
x_542 = lean_array_uset(x_524, x_528, x_541);
lean_inc(x_516);
lean_inc(x_354);
x_543 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectLevelAux_spec__5___redArg(x_354, x_516, x_529);
x_544 = lean_array_uset(x_542, x_528, x_543);
lean_ctor_set(x_520, 1, x_544);
x_473 = x_521;
x_474 = x_516;
x_475 = x_519;
x_476 = x_520;
goto block_491;
}
}
else
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; size_t x_548; size_t x_549; size_t x_550; lean_object* x_551; uint8_t x_552; 
x_545 = lean_ctor_get(x_520, 0);
x_546 = lean_ctor_get(x_520, 1);
lean_inc(x_546);
lean_inc(x_545);
lean_dec(x_520);
x_547 = lean_array_get_size(x_546);
x_548 = lean_usize_of_nat(x_547);
lean_dec(x_547);
x_549 = lean_usize_sub(x_548, x_510);
x_550 = lean_usize_land(x_507, x_549);
x_551 = lean_array_uget(x_546, x_550);
x_552 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___redArg(x_354, x_551);
if (x_552 == 0)
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; uint8_t x_561; 
x_553 = lean_nat_add(x_545, x_509);
lean_dec(x_545);
lean_inc(x_516);
lean_inc(x_354);
x_554 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_554, 0, x_354);
lean_ctor_set(x_554, 1, x_516);
lean_ctor_set(x_554, 2, x_551);
x_555 = lean_array_uset(x_546, x_550, x_554);
x_556 = lean_unsigned_to_nat(2u);
x_557 = lean_nat_shiftl(x_553, x_556);
x_558 = lean_unsigned_to_nat(3u);
x_559 = lean_nat_div(x_557, x_558);
lean_dec(x_557);
x_560 = lean_array_get_size(x_555);
x_561 = lean_nat_dec_le(x_559, x_560);
lean_dec(x_560);
lean_dec(x_559);
if (x_561 == 0)
{
lean_object* x_562; lean_object* x_563; 
x_562 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2___redArg(x_555);
x_563 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_563, 0, x_553);
lean_ctor_set(x_563, 1, x_562);
x_473 = x_521;
x_474 = x_516;
x_475 = x_519;
x_476 = x_563;
goto block_491;
}
else
{
lean_object* x_564; 
x_564 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_564, 0, x_553);
lean_ctor_set(x_564, 1, x_555);
x_473 = x_521;
x_474 = x_516;
x_475 = x_519;
x_476 = x_564;
goto block_491;
}
}
else
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; 
x_565 = lean_box(0);
x_566 = lean_array_uset(x_546, x_550, x_565);
lean_inc(x_516);
lean_inc(x_354);
x_567 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectLevelAux_spec__5___redArg(x_354, x_516, x_551);
x_568 = lean_array_uset(x_566, x_550, x_567);
x_569 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_569, 0, x_545);
lean_ctor_set(x_569, 1, x_568);
x_473 = x_521;
x_474 = x_516;
x_475 = x_519;
x_476 = x_569;
goto block_491;
}
}
}
else
{
lean_object* x_570; 
x_570 = lean_ctor_get(x_514, 0);
lean_inc(x_570);
lean_dec(x_514);
x_468 = x_570;
x_469 = x_495;
goto block_472;
}
}
}
default: 
{
lean_object* x_574; 
x_574 = l_Lean_Meta_Closure_mkNewLevelParam___redArg(x_1, x_2, x_3);
return x_574;
}
}
block_12:
{
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = l_Lean_mkLevelIMax_x27(x_4, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_simpLevelIMax_x27(x_4, x_6, x_1);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
}
block_21:
{
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_17 = l_Lean_mkLevelMax_x27(x_15, x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Lean_simpLevelMax_x27(x_15, x_14, x_1);
lean_dec(x_1);
lean_dec(x_14);
lean_dec(x_15);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_13);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Closure_collectLevelAux___redArg(x_1, x_3, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectLevelAux_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectLevelAux_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectLevelAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectLevelAux_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Closure_collectLevelAux___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_Closure_collectLevelAux(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_163; 
x_163 = l_Lean_Level_hasMVar(x_1);
if (x_163 == 0)
{
uint8_t x_164; 
x_164 = l_Lean_Level_hasParam(x_1);
if (x_164 == 0)
{
lean_object* x_165; 
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_1);
lean_ctor_set(x_165, 1, x_3);
return x_165;
}
else
{
goto block_162;
}
}
else
{
goto block_162;
}
block_25:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 4);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 5);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 6);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 7);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 8);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 9);
lean_inc(x_16);
x_17 = lean_ctor_get(x_6, 10);
lean_inc(x_17);
x_18 = lean_ctor_get(x_6, 11);
lean_inc(x_18);
lean_dec(x_6);
x_19 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_8);
lean_ctor_set(x_19, 2, x_9);
lean_ctor_set(x_19, 3, x_10);
lean_ctor_set(x_19, 4, x_11);
lean_ctor_set(x_19, 5, x_12);
lean_ctor_set(x_19, 6, x_13);
lean_ctor_set(x_19, 7, x_14);
lean_ctor_set(x_19, 8, x_15);
lean_ctor_set(x_19, 9, x_16);
lean_ctor_set(x_19, 10, x_17);
lean_ctor_set(x_19, 11, x_18);
x_20 = lean_st_ref_set(x_2, x_19, x_5);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_4);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
block_162:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_st_ref_get(x_2, x_3);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint64_t x_34; lean_object* x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; lean_object* x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; size_t x_43; size_t x_44; lean_object* x_45; size_t x_46; size_t x_47; size_t x_48; lean_object* x_49; lean_object* x_50; 
x_30 = lean_ctor_get(x_26, 1);
x_31 = lean_ctor_get(x_26, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_array_get_size(x_32);
x_34 = l_Lean_Level_hash(x_1);
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
lean_dec(x_32);
x_50 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectLevelAux_spec__0___redArg(x_1, x_49);
lean_dec(x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_free_object(x_26);
lean_inc(x_1);
x_51 = l_Lean_Meta_Closure_collectLevelAux___redArg(x_1, x_2, x_30);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_st_ref_take(x_2, x_53);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = !lean_is_exclusive(x_56);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; size_t x_62; size_t x_63; size_t x_64; lean_object* x_65; uint8_t x_66; 
x_59 = lean_ctor_get(x_56, 0);
x_60 = lean_ctor_get(x_56, 1);
x_61 = lean_array_get_size(x_60);
x_62 = lean_usize_of_nat(x_61);
lean_dec(x_61);
x_63 = lean_usize_sub(x_62, x_46);
x_64 = lean_usize_land(x_43, x_63);
x_65 = lean_array_uget(x_60, x_64);
x_66 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___redArg(x_1, x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_67 = lean_nat_add(x_59, x_45);
lean_dec(x_59);
lean_inc(x_52);
x_68 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_68, 0, x_1);
lean_ctor_set(x_68, 1, x_52);
lean_ctor_set(x_68, 2, x_65);
x_69 = lean_array_uset(x_60, x_64, x_68);
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
x_76 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2___redArg(x_69);
lean_ctor_set(x_56, 1, x_76);
lean_ctor_set(x_56, 0, x_67);
x_4 = x_52;
x_5 = x_57;
x_6 = x_55;
x_7 = x_56;
goto block_25;
}
else
{
lean_ctor_set(x_56, 1, x_69);
lean_ctor_set(x_56, 0, x_67);
x_4 = x_52;
x_5 = x_57;
x_6 = x_55;
x_7 = x_56;
goto block_25;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_box(0);
x_78 = lean_array_uset(x_60, x_64, x_77);
lean_inc(x_52);
x_79 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectLevelAux_spec__5___redArg(x_1, x_52, x_65);
x_80 = lean_array_uset(x_78, x_64, x_79);
lean_ctor_set(x_56, 1, x_80);
x_4 = x_52;
x_5 = x_57;
x_6 = x_55;
x_7 = x_56;
goto block_25;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; size_t x_84; size_t x_85; size_t x_86; lean_object* x_87; uint8_t x_88; 
x_81 = lean_ctor_get(x_56, 0);
x_82 = lean_ctor_get(x_56, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_56);
x_83 = lean_array_get_size(x_82);
x_84 = lean_usize_of_nat(x_83);
lean_dec(x_83);
x_85 = lean_usize_sub(x_84, x_46);
x_86 = lean_usize_land(x_43, x_85);
x_87 = lean_array_uget(x_82, x_86);
x_88 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___redArg(x_1, x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_89 = lean_nat_add(x_81, x_45);
lean_dec(x_81);
lean_inc(x_52);
x_90 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_90, 0, x_1);
lean_ctor_set(x_90, 1, x_52);
lean_ctor_set(x_90, 2, x_87);
x_91 = lean_array_uset(x_82, x_86, x_90);
x_92 = lean_unsigned_to_nat(2u);
x_93 = lean_nat_shiftl(x_89, x_92);
x_94 = lean_unsigned_to_nat(3u);
x_95 = lean_nat_div(x_93, x_94);
lean_dec(x_93);
x_96 = lean_array_get_size(x_91);
x_97 = lean_nat_dec_le(x_95, x_96);
lean_dec(x_96);
lean_dec(x_95);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2___redArg(x_91);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_89);
lean_ctor_set(x_99, 1, x_98);
x_4 = x_52;
x_5 = x_57;
x_6 = x_55;
x_7 = x_99;
goto block_25;
}
else
{
lean_object* x_100; 
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_89);
lean_ctor_set(x_100, 1, x_91);
x_4 = x_52;
x_5 = x_57;
x_6 = x_55;
x_7 = x_100;
goto block_25;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_101 = lean_box(0);
x_102 = lean_array_uset(x_82, x_86, x_101);
lean_inc(x_52);
x_103 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectLevelAux_spec__5___redArg(x_1, x_52, x_87);
x_104 = lean_array_uset(x_102, x_86, x_103);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_81);
lean_ctor_set(x_105, 1, x_104);
x_4 = x_52;
x_5 = x_57;
x_6 = x_55;
x_7 = x_105;
goto block_25;
}
}
}
else
{
lean_object* x_106; 
lean_dec(x_1);
x_106 = lean_ctor_get(x_50, 0);
lean_inc(x_106);
lean_dec(x_50);
lean_ctor_set(x_26, 0, x_106);
return x_26;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; uint64_t x_110; lean_object* x_111; uint64_t x_112; uint64_t x_113; uint64_t x_114; lean_object* x_115; uint64_t x_116; uint64_t x_117; uint64_t x_118; size_t x_119; size_t x_120; lean_object* x_121; size_t x_122; size_t x_123; size_t x_124; lean_object* x_125; lean_object* x_126; 
x_107 = lean_ctor_get(x_26, 1);
lean_inc(x_107);
lean_dec(x_26);
x_108 = lean_ctor_get(x_28, 1);
lean_inc(x_108);
lean_dec(x_28);
x_109 = lean_array_get_size(x_108);
x_110 = l_Lean_Level_hash(x_1);
x_111 = lean_unsigned_to_nat(32u);
x_112 = lean_uint64_of_nat(x_111);
x_113 = lean_uint64_shift_right(x_110, x_112);
x_114 = lean_uint64_xor(x_110, x_113);
x_115 = lean_unsigned_to_nat(16u);
x_116 = lean_uint64_of_nat(x_115);
x_117 = lean_uint64_shift_right(x_114, x_116);
x_118 = lean_uint64_xor(x_114, x_117);
x_119 = lean_uint64_to_usize(x_118);
x_120 = lean_usize_of_nat(x_109);
lean_dec(x_109);
x_121 = lean_unsigned_to_nat(1u);
x_122 = lean_usize_of_nat(x_121);
x_123 = lean_usize_sub(x_120, x_122);
x_124 = lean_usize_land(x_119, x_123);
x_125 = lean_array_uget(x_108, x_124);
lean_dec(x_108);
x_126 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Closure_collectLevelAux_spec__0___redArg(x_1, x_125);
lean_dec(x_125);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; size_t x_138; size_t x_139; size_t x_140; lean_object* x_141; uint8_t x_142; 
lean_inc(x_1);
x_127 = l_Lean_Meta_Closure_collectLevelAux___redArg(x_1, x_2, x_107);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_st_ref_take(x_2, x_129);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
lean_dec(x_130);
x_134 = lean_ctor_get(x_132, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_132, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_136 = x_132;
} else {
 lean_dec_ref(x_132);
 x_136 = lean_box(0);
}
x_137 = lean_array_get_size(x_135);
x_138 = lean_usize_of_nat(x_137);
lean_dec(x_137);
x_139 = lean_usize_sub(x_138, x_122);
x_140 = lean_usize_land(x_119, x_139);
x_141 = lean_array_uget(x_135, x_140);
x_142 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Closure_collectLevelAux_spec__1___redArg(x_1, x_141);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_143 = lean_nat_add(x_134, x_121);
lean_dec(x_134);
lean_inc(x_128);
x_144 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_144, 0, x_1);
lean_ctor_set(x_144, 1, x_128);
lean_ctor_set(x_144, 2, x_141);
x_145 = lean_array_uset(x_135, x_140, x_144);
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
x_152 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Closure_collectLevelAux_spec__2___redArg(x_145);
if (lean_is_scalar(x_136)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_136;
}
lean_ctor_set(x_153, 0, x_143);
lean_ctor_set(x_153, 1, x_152);
x_4 = x_128;
x_5 = x_133;
x_6 = x_131;
x_7 = x_153;
goto block_25;
}
else
{
lean_object* x_154; 
if (lean_is_scalar(x_136)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_136;
}
lean_ctor_set(x_154, 0, x_143);
lean_ctor_set(x_154, 1, x_145);
x_4 = x_128;
x_5 = x_133;
x_6 = x_131;
x_7 = x_154;
goto block_25;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_155 = lean_box(0);
x_156 = lean_array_uset(x_135, x_140, x_155);
lean_inc(x_128);
x_157 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Closure_collectLevelAux_spec__5___redArg(x_1, x_128, x_141);
x_158 = lean_array_uset(x_156, x_140, x_157);
if (lean_is_scalar(x_136)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_136;
}
lean_ctor_set(x_159, 0, x_134);
lean_ctor_set(x_159, 1, x_158);
x_4 = x_128;
x_5 = x_133;
x_6 = x_131;
x_7 = x_159;
goto block_25;
}
}
else
{
lean_object* x_160; lean_object* x_161; 
lean_dec(x_1);
x_160 = lean_ctor_get(x_126, 0);
lean_inc(x_160);
lean_dec(x_126);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_107);
return x_161;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Closure_collectLevel___redArg(x_1, x_3, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Closure_collectLevel___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_Closure_collectLevel(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Closure_preprocess_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Closure_preprocess_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_instantiateMVars___at___Lean_Meta_Closure_preprocess_spec__0___redArg(x_1, x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_instantiateMVars___at___Lean_Meta_Closure_preprocess_spec__0___redArg(x_1, x_5, x_8);
if (x_2 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_10);
x_12 = l_Lean_Meta_check(x_10, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_10);
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Closure_preprocess_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___Lean_Meta_Closure_preprocess_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Closure_preprocess_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_instantiateMVars___at___Lean_Meta_Closure_preprocess_spec__0(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_Closure_preprocess(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
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
x_13 = lean_ctor_get(x_7, 4);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 5);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 6);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 7);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 8);
lean_inc(x_17);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_17, x_18);
lean_dec(x_17);
x_20 = lean_ctor_get(x_7, 9);
lean_inc(x_20);
x_21 = lean_ctor_get(x_7, 10);
lean_inc(x_21);
x_22 = lean_ctor_get(x_7, 11);
lean_inc(x_22);
lean_dec(x_7);
x_23 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_23, 0, x_9);
lean_ctor_set(x_23, 1, x_10);
lean_ctor_set(x_23, 2, x_11);
lean_ctor_set(x_23, 3, x_12);
lean_ctor_set(x_23, 4, x_13);
lean_ctor_set(x_23, 5, x_14);
lean_ctor_set(x_23, 6, x_15);
lean_ctor_set(x_23, 7, x_16);
lean_ctor_set(x_23, 8, x_19);
lean_ctor_set(x_23, 9, x_20);
lean_ctor_set(x_23, 10, x_21);
lean_ctor_set(x_23, 11, x_22);
x_24 = lean_st_ref_set(x_1, x_23, x_8);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = lean_mk_string_unchecked("_x", 2, 2);
x_28 = l_Lean_Name_mkStr1(x_27);
x_29 = lean_ctor_get(x_4, 8);
lean_inc(x_29);
lean_dec(x_4);
x_30 = lean_name_append_index_after(x_28, x_29);
lean_ctor_set(x_24, 0, x_30);
return x_24;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_dec(x_24);
x_32 = lean_mk_string_unchecked("_x", 2, 2);
x_33 = l_Lean_Name_mkStr1(x_32);
x_34 = lean_ctor_get(x_4, 8);
lean_inc(x_34);
lean_dec(x_4);
x_35 = lean_name_append_index_after(x_33, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_31);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Closure_mkNextUserName___redArg(x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Closure_mkNextUserName___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_Meta_Closure_mkNextUserName(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
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
x_15 = lean_ctor_get(x_5, 8);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 9);
lean_inc(x_16);
x_17 = lean_ctor_get(x_5, 10);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 11);
lean_inc(x_18);
lean_dec(x_5);
x_19 = lean_array_push(x_18, x_1);
x_20 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_8);
lean_ctor_set(x_20, 2, x_9);
lean_ctor_set(x_20, 3, x_10);
lean_ctor_set(x_20, 4, x_11);
lean_ctor_set(x_20, 5, x_12);
lean_ctor_set(x_20, 6, x_13);
lean_ctor_set(x_20, 7, x_14);
lean_ctor_set(x_20, 8, x_15);
lean_ctor_set(x_20, 9, x_16);
lean_ctor_set(x_20, 10, x_17);
lean_ctor_set(x_20, 11, x_19);
x_21 = lean_st_ref_set(x_2, x_20, x_6);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Closure_pushToProcess___redArg(x_1, x_3, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Closure_pushToProcess___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_Closure_pushToProcess(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Meta_Closure_collectExprAux_spec__0_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___Lean_Meta_Closure_collectExprAux_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___Lean_Meta_Closure_collectExprAux_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(x_7, x_1);
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
x_12 = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(x_11, x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___Lean_Meta_Closure_collectExprAux_spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_getDelayedMVarAssignment_x3f___at___Lean_Meta_Closure_collectExprAux_spec__2___redArg(x_1, x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_Closure_collectExprAux_spec__3___redArg___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(x_2);
x_12 = lean_apply_9(x_1, x_4, x_5, x_11, x_3, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_Closure_collectExprAux_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_box(x_5);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_Closure_collectExprAux_spec__3___redArg___lam__0___boxed), 10, 3);
lean_closure_set(x_13, 0, x_3);
lean_closure_set(x_13, 1, x_12);
lean_closure_set(x_13, 2, x_6);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___redArg(x_1, x_2, x_13, x_4, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_Closure_collectExprAux_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_Closure_collectExprAux_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_Closure_collectExprAux_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_List_reverse___redArg(x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = l_Lean_Meta_Closure_collectLevel___redArg(x_8, x_3, x_4);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_11);
{
lean_object* _tmp_0 = x_9;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_3 = x_12;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_16 = l_Lean_Meta_Closure_collectLevel___redArg(x_14, x_3, x_4);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_2);
x_1 = x_15;
x_2 = x_19;
x_4 = x_18;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_Closure_collectExprAux_spec__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_mapM_loop___at___Lean_Meta_Closure_collectExprAux_spec__4___redArg(x_1, x_2, x_4, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_171; 
x_171 = l_Lean_Expr_hasLevelParam(x_1);
if (x_171 == 0)
{
uint8_t x_172; 
x_172 = l_Lean_Expr_hasFVar(x_1);
if (x_172 == 0)
{
uint8_t x_173; 
x_173 = l_Lean_Expr_hasMVar(x_1);
if (x_173 == 0)
{
lean_object* x_174; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_1);
lean_ctor_set(x_174, 1, x_8);
return x_174;
}
else
{
goto block_170;
}
}
else
{
goto block_170;
}
}
else
{
goto block_170;
}
block_30:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
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
x_20 = lean_ctor_get(x_10, 8);
lean_inc(x_20);
x_21 = lean_ctor_get(x_10, 9);
lean_inc(x_21);
x_22 = lean_ctor_get(x_10, 10);
lean_inc(x_22);
x_23 = lean_ctor_get(x_10, 11);
lean_inc(x_23);
lean_dec(x_10);
x_24 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_24, 0, x_9);
lean_ctor_set(x_24, 1, x_13);
lean_ctor_set(x_24, 2, x_14);
lean_ctor_set(x_24, 3, x_15);
lean_ctor_set(x_24, 4, x_16);
lean_ctor_set(x_24, 5, x_17);
lean_ctor_set(x_24, 6, x_18);
lean_ctor_set(x_24, 7, x_19);
lean_ctor_set(x_24, 8, x_20);
lean_ctor_set(x_24, 9, x_21);
lean_ctor_set(x_24, 10, x_22);
lean_ctor_set(x_24, 11, x_23);
x_25 = lean_st_ref_set(x_3, x_24, x_12);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_11);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_11);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
block_170:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_st_ref_get(x_3, x_8);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint64_t x_39; lean_object* x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; lean_object* x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; size_t x_48; size_t x_49; lean_object* x_50; size_t x_51; size_t x_52; size_t x_53; lean_object* x_54; lean_object* x_55; 
x_35 = lean_ctor_get(x_31, 1);
x_36 = lean_ctor_get(x_31, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
x_38 = lean_array_get_size(x_37);
x_39 = l_Lean_Expr_hash(x_1);
x_40 = lean_unsigned_to_nat(32u);
x_41 = lean_uint64_of_nat(x_40);
x_42 = lean_uint64_shift_right(x_39, x_41);
x_43 = lean_uint64_xor(x_39, x_42);
x_44 = lean_unsigned_to_nat(16u);
x_45 = lean_uint64_of_nat(x_44);
x_46 = lean_uint64_shift_right(x_43, x_45);
x_47 = lean_uint64_xor(x_43, x_46);
x_48 = lean_uint64_to_usize(x_47);
x_49 = lean_usize_of_nat(x_38);
lean_dec(x_38);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_usize_of_nat(x_50);
x_52 = lean_usize_sub(x_49, x_51);
x_53 = lean_usize_land(x_48, x_52);
x_54 = lean_array_uget(x_37, x_53);
lean_dec(x_37);
x_55 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__0(lean_box(0), x_1, x_54);
lean_dec(x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; 
lean_free_object(x_31);
lean_inc(x_3);
lean_inc(x_1);
x_56 = l_Lean_Meta_Closure_collectExprAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_35);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_st_ref_take(x_3, x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_63 = !lean_is_exclusive(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; size_t x_68; size_t x_69; size_t x_70; lean_object* x_71; uint8_t x_72; 
x_64 = lean_ctor_get(x_61, 0);
x_65 = lean_ctor_get(x_61, 1);
x_66 = lean_ctor_get(x_60, 0);
lean_inc(x_66);
x_67 = lean_array_get_size(x_65);
x_68 = lean_usize_of_nat(x_67);
lean_dec(x_67);
x_69 = lean_usize_sub(x_68, x_51);
x_70 = lean_usize_land(x_48, x_69);
x_71 = lean_array_uget(x_65, x_70);
x_72 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__1(lean_box(0), x_1, x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_73 = lean_nat_add(x_64, x_50);
lean_dec(x_64);
lean_inc(x_57);
x_74 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_74, 0, x_1);
lean_ctor_set(x_74, 1, x_57);
lean_ctor_set(x_74, 2, x_71);
x_75 = lean_array_uset(x_65, x_70, x_74);
x_76 = lean_unsigned_to_nat(2u);
x_77 = lean_nat_shiftl(x_73, x_76);
x_78 = lean_unsigned_to_nat(3u);
x_79 = lean_nat_div(x_77, x_78);
lean_dec(x_77);
x_80 = lean_array_get_size(x_75);
x_81 = lean_nat_dec_le(x_79, x_80);
lean_dec(x_80);
lean_dec(x_79);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2(lean_box(0), x_75);
lean_ctor_set(x_61, 1, x_82);
lean_ctor_set(x_61, 0, x_73);
x_9 = x_66;
x_10 = x_60;
x_11 = x_57;
x_12 = x_62;
x_13 = x_61;
goto block_30;
}
else
{
lean_ctor_set(x_61, 1, x_75);
lean_ctor_set(x_61, 0, x_73);
x_9 = x_66;
x_10 = x_60;
x_11 = x_57;
x_12 = x_62;
x_13 = x_61;
goto block_30;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_box(0);
x_84 = lean_array_uset(x_65, x_70, x_83);
lean_inc(x_57);
x_85 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__5(lean_box(0), x_1, x_57, x_71);
x_86 = lean_array_uset(x_84, x_70, x_85);
lean_ctor_set(x_61, 1, x_86);
x_9 = x_66;
x_10 = x_60;
x_11 = x_57;
x_12 = x_62;
x_13 = x_61;
goto block_30;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; size_t x_91; size_t x_92; size_t x_93; lean_object* x_94; uint8_t x_95; 
x_87 = lean_ctor_get(x_61, 0);
x_88 = lean_ctor_get(x_61, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_61);
x_89 = lean_ctor_get(x_60, 0);
lean_inc(x_89);
x_90 = lean_array_get_size(x_88);
x_91 = lean_usize_of_nat(x_90);
lean_dec(x_90);
x_92 = lean_usize_sub(x_91, x_51);
x_93 = lean_usize_land(x_48, x_92);
x_94 = lean_array_uget(x_88, x_93);
x_95 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__1(lean_box(0), x_1, x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_96 = lean_nat_add(x_87, x_50);
lean_dec(x_87);
lean_inc(x_57);
x_97 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_97, 0, x_1);
lean_ctor_set(x_97, 1, x_57);
lean_ctor_set(x_97, 2, x_94);
x_98 = lean_array_uset(x_88, x_93, x_97);
x_99 = lean_unsigned_to_nat(2u);
x_100 = lean_nat_shiftl(x_96, x_99);
x_101 = lean_unsigned_to_nat(3u);
x_102 = lean_nat_div(x_100, x_101);
lean_dec(x_100);
x_103 = lean_array_get_size(x_98);
x_104 = lean_nat_dec_le(x_102, x_103);
lean_dec(x_103);
lean_dec(x_102);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2(lean_box(0), x_98);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_96);
lean_ctor_set(x_106, 1, x_105);
x_9 = x_89;
x_10 = x_60;
x_11 = x_57;
x_12 = x_62;
x_13 = x_106;
goto block_30;
}
else
{
lean_object* x_107; 
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_96);
lean_ctor_set(x_107, 1, x_98);
x_9 = x_89;
x_10 = x_60;
x_11 = x_57;
x_12 = x_62;
x_13 = x_107;
goto block_30;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_108 = lean_box(0);
x_109 = lean_array_uset(x_88, x_93, x_108);
lean_inc(x_57);
x_110 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__5(lean_box(0), x_1, x_57, x_94);
x_111 = lean_array_uset(x_109, x_93, x_110);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_87);
lean_ctor_set(x_112, 1, x_111);
x_9 = x_89;
x_10 = x_60;
x_11 = x_57;
x_12 = x_62;
x_13 = x_112;
goto block_30;
}
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_56;
}
}
else
{
lean_object* x_113; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_113 = lean_ctor_get(x_55, 0);
lean_inc(x_113);
lean_dec(x_55);
lean_ctor_set(x_31, 0, x_113);
return x_31;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint64_t x_117; lean_object* x_118; uint64_t x_119; uint64_t x_120; uint64_t x_121; lean_object* x_122; uint64_t x_123; uint64_t x_124; uint64_t x_125; size_t x_126; size_t x_127; lean_object* x_128; size_t x_129; size_t x_130; size_t x_131; lean_object* x_132; lean_object* x_133; 
x_114 = lean_ctor_get(x_31, 1);
lean_inc(x_114);
lean_dec(x_31);
x_115 = lean_ctor_get(x_33, 1);
lean_inc(x_115);
lean_dec(x_33);
x_116 = lean_array_get_size(x_115);
x_117 = l_Lean_Expr_hash(x_1);
x_118 = lean_unsigned_to_nat(32u);
x_119 = lean_uint64_of_nat(x_118);
x_120 = lean_uint64_shift_right(x_117, x_119);
x_121 = lean_uint64_xor(x_117, x_120);
x_122 = lean_unsigned_to_nat(16u);
x_123 = lean_uint64_of_nat(x_122);
x_124 = lean_uint64_shift_right(x_121, x_123);
x_125 = lean_uint64_xor(x_121, x_124);
x_126 = lean_uint64_to_usize(x_125);
x_127 = lean_usize_of_nat(x_116);
lean_dec(x_116);
x_128 = lean_unsigned_to_nat(1u);
x_129 = lean_usize_of_nat(x_128);
x_130 = lean_usize_sub(x_127, x_129);
x_131 = lean_usize_land(x_126, x_130);
x_132 = lean_array_uget(x_115, x_131);
lean_dec(x_115);
x_133 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__0(lean_box(0), x_1, x_132);
lean_dec(x_132);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; 
lean_inc(x_3);
lean_inc(x_1);
x_134 = l_Lean_Meta_Closure_collectExprAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_114);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; size_t x_146; size_t x_147; size_t x_148; lean_object* x_149; uint8_t x_150; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_st_ref_take(x_3, x_136);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
lean_dec(x_137);
x_141 = lean_ctor_get(x_139, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_139, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_143 = x_139;
} else {
 lean_dec_ref(x_139);
 x_143 = lean_box(0);
}
x_144 = lean_ctor_get(x_138, 0);
lean_inc(x_144);
x_145 = lean_array_get_size(x_142);
x_146 = lean_usize_of_nat(x_145);
lean_dec(x_145);
x_147 = lean_usize_sub(x_146, x_129);
x_148 = lean_usize_land(x_126, x_147);
x_149 = lean_array_uget(x_142, x_148);
x_150 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__1(lean_box(0), x_1, x_149);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_151 = lean_nat_add(x_141, x_128);
lean_dec(x_141);
lean_inc(x_135);
x_152 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_152, 0, x_1);
lean_ctor_set(x_152, 1, x_135);
lean_ctor_set(x_152, 2, x_149);
x_153 = lean_array_uset(x_142, x_148, x_152);
x_154 = lean_unsigned_to_nat(2u);
x_155 = lean_nat_shiftl(x_151, x_154);
x_156 = lean_unsigned_to_nat(3u);
x_157 = lean_nat_div(x_155, x_156);
lean_dec(x_155);
x_158 = lean_array_get_size(x_153);
x_159 = lean_nat_dec_le(x_157, x_158);
lean_dec(x_158);
lean_dec(x_157);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; 
x_160 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2(lean_box(0), x_153);
if (lean_is_scalar(x_143)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_143;
}
lean_ctor_set(x_161, 0, x_151);
lean_ctor_set(x_161, 1, x_160);
x_9 = x_144;
x_10 = x_138;
x_11 = x_135;
x_12 = x_140;
x_13 = x_161;
goto block_30;
}
else
{
lean_object* x_162; 
if (lean_is_scalar(x_143)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_143;
}
lean_ctor_set(x_162, 0, x_151);
lean_ctor_set(x_162, 1, x_153);
x_9 = x_144;
x_10 = x_138;
x_11 = x_135;
x_12 = x_140;
x_13 = x_162;
goto block_30;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_163 = lean_box(0);
x_164 = lean_array_uset(x_142, x_148, x_163);
lean_inc(x_135);
x_165 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__5(lean_box(0), x_1, x_135, x_149);
x_166 = lean_array_uset(x_164, x_148, x_165);
if (lean_is_scalar(x_143)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_143;
}
lean_ctor_set(x_167, 0, x_141);
lean_ctor_set(x_167, 1, x_166);
x_9 = x_144;
x_10 = x_138;
x_11 = x_135;
x_12 = x_140;
x_13 = x_167;
goto block_30;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_134;
}
}
else
{
lean_object* x_168; lean_object* x_169; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_168 = lean_ctor_get(x_133, 0);
lean_inc(x_168);
lean_dec(x_133);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_114);
return x_169;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_11 = l_Lean_mkAppN(x_1, x_2);
x_12 = lean_box(0);
x_13 = lean_box(1);
x_14 = lean_box(1);
x_15 = lean_unbox(x_12);
x_16 = lean_unbox(x_13);
x_17 = lean_unbox(x_12);
x_18 = lean_unbox(x_14);
x_19 = l_Lean_Meta_mkLambdaFVars(x_2, x_11, x_15, x_16, x_17, x_18, x_6, x_7, x_8, x_9, x_10);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
lean_inc(x_4);
lean_inc(x_9);
x_10 = l_Lean_FVarId_getValue_x3f___redArg(x_9, x_4, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
if (x_2 == 0)
{
lean_dec(x_11);
x_13 = x_2;
x_14 = x_3;
x_15 = x_4;
x_16 = x_5;
x_17 = x_6;
x_18 = x_7;
goto block_38;
}
else
{
if (lean_obj_tag(x_11) == 0)
{
x_13 = x_2;
x_14 = x_3;
x_15 = x_4;
x_16 = x_5;
x_17 = x_6;
x_18 = x_7;
goto block_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_9);
x_39 = lean_ctor_get(x_11, 0);
lean_inc(x_39);
lean_dec(x_11);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_40 = l_Lean_Meta_Closure_preprocess(x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Meta_Closure_collectExprAux___lam__0(x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_42);
return x_43;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_40;
}
}
}
block_38:
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_mkFreshFVarId___at___Lean_Meta_Closure_collectExprAux_spec__0(x_13, x_14, x_15, x_16, x_17, x_18, x_12);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_ctor_set(x_19, 1, x_21);
lean_ctor_set(x_19, 0, x_9);
x_23 = l_Lean_Meta_Closure_pushToProcess___redArg(x_19, x_14, x_22);
lean_dec(x_14);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = l_Lean_Expr_fvar___override(x_21);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = l_Lean_Expr_fvar___override(x_21);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_19, 0);
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_19);
lean_inc(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_9);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_Lean_Meta_Closure_pushToProcess___redArg(x_32, x_14, x_31);
lean_dec(x_14);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
x_36 = l_Lean_Expr_fvar___override(x_30);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_10);
if (x_44 == 0)
{
return x_10;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_10, 0);
x_46 = lean_ctor_get(x_10, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_10);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
case 2:
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_inc(x_48);
x_49 = l_Lean_MVarId_getDecl(x_48, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_ctor_get(x_50, 2);
lean_inc(x_52);
lean_dec(x_50);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_52);
x_53 = l_Lean_Meta_Closure_preprocess(x_52, x_2, x_3, x_4, x_5, x_6, x_7, x_51);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_56 = l_Lean_Meta_Closure_collectExprAux___lam__0(x_54, x_2, x_3, x_4, x_5, x_6, x_7, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_100; lean_object* x_101; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_mkFreshFVarId___at___Lean_Meta_Closure_collectExprAux_spec__0(x_2, x_3, x_4, x_5, x_6, x_7, x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_Meta_Closure_mkNextUserName___redArg(x_3, x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_100 = l_Lean_getDelayedMVarAssignment_x3f___at___Lean_Meta_Closure_collectExprAux_spec__2___redArg(x_48, x_5, x_64);
lean_dec(x_48);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; 
lean_dec(x_52);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_65 = x_1;
x_66 = x_3;
x_67 = x_102;
goto block_99;
}
else
{
uint8_t x_103; 
x_103 = !lean_is_exclusive(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; 
x_104 = lean_ctor_get(x_101, 0);
x_105 = lean_ctor_get(x_100, 1);
lean_inc(x_105);
lean_dec(x_100);
x_106 = lean_ctor_get(x_104, 0);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_alloc_closure((void*)(l_Lean_Meta_Closure_collectExprAux___lam__1___boxed), 10, 1);
lean_closure_set(x_107, 0, x_1);
x_108 = lean_array_get_size(x_106);
lean_dec(x_106);
lean_ctor_set(x_101, 0, x_108);
x_109 = lean_box(0);
x_110 = lean_unbox(x_109);
lean_inc(x_3);
x_111 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_Closure_collectExprAux_spec__3___redArg(x_52, x_101, x_107, x_110, x_2, x_3, x_4, x_5, x_6, x_7, x_105);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_65 = x_112;
x_66 = x_3;
x_67 = x_113;
goto block_99;
}
else
{
lean_dec(x_63);
lean_dec(x_60);
lean_dec(x_57);
lean_dec(x_3);
return x_111;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; 
x_114 = lean_ctor_get(x_101, 0);
lean_inc(x_114);
lean_dec(x_101);
x_115 = lean_ctor_get(x_100, 1);
lean_inc(x_115);
lean_dec(x_100);
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_116);
lean_dec(x_114);
x_117 = lean_alloc_closure((void*)(l_Lean_Meta_Closure_collectExprAux___lam__1___boxed), 10, 1);
lean_closure_set(x_117, 0, x_1);
x_118 = lean_array_get_size(x_116);
lean_dec(x_116);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_118);
x_120 = lean_box(0);
x_121 = lean_unbox(x_120);
lean_inc(x_3);
x_122 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_Closure_collectExprAux_spec__3___redArg(x_52, x_119, x_117, x_121, x_2, x_3, x_4, x_5, x_6, x_7, x_115);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_65 = x_123;
x_66 = x_3;
x_67 = x_124;
goto block_99;
}
else
{
lean_dec(x_63);
lean_dec(x_60);
lean_dec(x_57);
lean_dec(x_3);
return x_122;
}
}
}
block_99:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_68 = lean_st_ref_take(x_66, x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_69, 2);
lean_inc(x_73);
x_74 = lean_ctor_get(x_69, 3);
lean_inc(x_74);
x_75 = lean_ctor_get(x_69, 4);
lean_inc(x_75);
x_76 = lean_ctor_get(x_69, 5);
lean_inc(x_76);
x_77 = lean_ctor_get(x_69, 6);
lean_inc(x_77);
x_78 = lean_box(0);
x_79 = lean_box(0);
x_80 = lean_box(0);
lean_inc(x_60);
x_81 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_60);
lean_ctor_set(x_81, 2, x_63);
lean_ctor_set(x_81, 3, x_57);
x_82 = lean_unbox(x_79);
lean_ctor_set_uint8(x_81, sizeof(void*)*4, x_82);
x_83 = lean_unbox(x_80);
lean_ctor_set_uint8(x_81, sizeof(void*)*4 + 1, x_83);
x_84 = lean_array_push(x_77, x_81);
x_85 = lean_ctor_get(x_69, 7);
lean_inc(x_85);
x_86 = lean_ctor_get(x_69, 8);
lean_inc(x_86);
x_87 = lean_ctor_get(x_69, 9);
lean_inc(x_87);
x_88 = lean_array_push(x_87, x_65);
x_89 = lean_ctor_get(x_69, 10);
lean_inc(x_89);
x_90 = lean_ctor_get(x_69, 11);
lean_inc(x_90);
lean_dec(x_69);
x_91 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_91, 0, x_71);
lean_ctor_set(x_91, 1, x_72);
lean_ctor_set(x_91, 2, x_73);
lean_ctor_set(x_91, 3, x_74);
lean_ctor_set(x_91, 4, x_75);
lean_ctor_set(x_91, 5, x_76);
lean_ctor_set(x_91, 6, x_84);
lean_ctor_set(x_91, 7, x_85);
lean_ctor_set(x_91, 8, x_86);
lean_ctor_set(x_91, 9, x_88);
lean_ctor_set(x_91, 10, x_89);
lean_ctor_set(x_91, 11, x_90);
x_92 = lean_st_ref_set(x_66, x_91, x_70);
lean_dec(x_66);
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_92, 0);
lean_dec(x_94);
x_95 = l_Lean_Expr_fvar___override(x_60);
lean_ctor_set(x_92, 0, x_95);
return x_92;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_92, 1);
lean_inc(x_96);
lean_dec(x_92);
x_97 = l_Lean_Expr_fvar___override(x_60);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
}
else
{
lean_dec(x_52);
lean_dec(x_48);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_56;
}
}
else
{
lean_dec(x_52);
lean_dec(x_48);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_53;
}
}
else
{
uint8_t x_125; 
lean_dec(x_48);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_125 = !lean_is_exclusive(x_49);
if (x_125 == 0)
{
return x_49;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_49, 0);
x_127 = lean_ctor_get(x_49, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_49);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
case 3:
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_129 = lean_ctor_get(x_1, 0);
lean_inc(x_129);
lean_inc(x_129);
x_130 = l_Lean_Meta_Closure_collectLevel___redArg(x_129, x_3, x_8);
lean_dec(x_3);
x_131 = !lean_is_exclusive(x_130);
if (x_131 == 0)
{
lean_object* x_132; size_t x_133; size_t x_134; uint8_t x_135; 
x_132 = lean_ctor_get(x_130, 0);
x_133 = lean_ptr_addr(x_129);
lean_dec(x_129);
x_134 = lean_ptr_addr(x_132);
x_135 = lean_usize_dec_eq(x_133, x_134);
if (x_135 == 0)
{
lean_object* x_136; 
lean_dec(x_1);
x_136 = l_Lean_Expr_sort___override(x_132);
lean_ctor_set(x_130, 0, x_136);
return x_130;
}
else
{
lean_dec(x_132);
lean_ctor_set(x_130, 0, x_1);
return x_130;
}
}
else
{
lean_object* x_137; lean_object* x_138; size_t x_139; size_t x_140; uint8_t x_141; 
x_137 = lean_ctor_get(x_130, 0);
x_138 = lean_ctor_get(x_130, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_130);
x_139 = lean_ptr_addr(x_129);
lean_dec(x_129);
x_140 = lean_ptr_addr(x_137);
x_141 = lean_usize_dec_eq(x_139, x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_1);
x_142 = l_Lean_Expr_sort___override(x_137);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_138);
return x_143;
}
else
{
lean_object* x_144; 
lean_dec(x_137);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_1);
lean_ctor_set(x_144, 1, x_138);
return x_144;
}
}
}
case 4:
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_145 = lean_ctor_get(x_1, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_1, 1);
lean_inc(x_146);
x_147 = lean_box(0);
lean_inc(x_146);
x_148 = l_List_mapM_loop___at___Lean_Meta_Closure_collectExprAux_spec__4___redArg(x_146, x_147, x_3, x_8);
lean_dec(x_3);
x_149 = !lean_is_exclusive(x_148);
if (x_149 == 0)
{
lean_object* x_150; uint8_t x_151; 
x_150 = lean_ctor_get(x_148, 0);
x_151 = l_ptrEqList___redArg(x_146, x_150);
lean_dec(x_146);
if (x_151 == 0)
{
lean_object* x_152; 
lean_dec(x_1);
x_152 = l_Lean_Expr_const___override(x_145, x_150);
lean_ctor_set(x_148, 0, x_152);
return x_148;
}
else
{
lean_dec(x_150);
lean_dec(x_145);
lean_ctor_set(x_148, 0, x_1);
return x_148;
}
}
else
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_153 = lean_ctor_get(x_148, 0);
x_154 = lean_ctor_get(x_148, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_148);
x_155 = l_ptrEqList___redArg(x_146, x_153);
lean_dec(x_146);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_1);
x_156 = l_Lean_Expr_const___override(x_145, x_153);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_154);
return x_157;
}
else
{
lean_object* x_158; 
lean_dec(x_153);
lean_dec(x_145);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_1);
lean_ctor_set(x_158, 1, x_154);
return x_158;
}
}
}
case 5:
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_1, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_1, 1);
lean_inc(x_160);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_159);
x_161 = l_Lean_Meta_Closure_collectExprAux___lam__0(x_159, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
lean_inc(x_160);
x_164 = l_Lean_Meta_Closure_collectExprAux___lam__0(x_160, x_2, x_3, x_4, x_5, x_6, x_7, x_163);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; size_t x_173; size_t x_174; uint8_t x_175; 
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
x_173 = lean_ptr_addr(x_159);
lean_dec(x_159);
x_174 = lean_ptr_addr(x_162);
x_175 = lean_usize_dec_eq(x_173, x_174);
if (x_175 == 0)
{
lean_dec(x_160);
x_168 = x_175;
goto block_172;
}
else
{
size_t x_176; size_t x_177; uint8_t x_178; 
x_176 = lean_ptr_addr(x_160);
lean_dec(x_160);
x_177 = lean_ptr_addr(x_165);
x_178 = lean_usize_dec_eq(x_176, x_177);
x_168 = x_178;
goto block_172;
}
block_172:
{
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; 
lean_dec(x_1);
x_169 = l_Lean_Expr_app___override(x_162, x_165);
if (lean_is_scalar(x_167)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_167;
}
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_166);
return x_170;
}
else
{
lean_object* x_171; 
lean_dec(x_165);
lean_dec(x_162);
if (lean_is_scalar(x_167)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_167;
}
lean_ctor_set(x_171, 0, x_1);
lean_ctor_set(x_171, 1, x_166);
return x_171;
}
}
}
else
{
lean_dec(x_162);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_1);
return x_164;
}
}
else
{
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_161;
}
}
case 6:
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; 
x_179 = lean_ctor_get(x_1, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_1, 1);
lean_inc(x_180);
x_181 = lean_ctor_get(x_1, 2);
lean_inc(x_181);
x_182 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_180);
x_183 = l_Lean_Meta_Closure_collectExprAux___lam__0(x_180, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
lean_inc(x_181);
x_186 = l_Lean_Meta_Closure_collectExprAux___lam__0(x_181, x_2, x_3, x_4, x_5, x_6, x_7, x_185);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_189 = x_186;
} else {
 lean_dec_ref(x_186);
 x_189 = lean_box(0);
}
x_190 = l_Lean_Expr_lam___override(x_179, x_180, x_181, x_182);
if (lean_obj_tag(x_190) == 6)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; uint8_t x_195; size_t x_203; size_t x_204; uint8_t x_205; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_190, 2);
lean_inc(x_193);
x_194 = lean_ctor_get_uint8(x_190, sizeof(void*)*3 + 8);
x_203 = lean_ptr_addr(x_192);
lean_dec(x_192);
x_204 = lean_ptr_addr(x_184);
x_205 = lean_usize_dec_eq(x_203, x_204);
if (x_205 == 0)
{
lean_dec(x_193);
x_195 = x_205;
goto block_202;
}
else
{
size_t x_206; size_t x_207; uint8_t x_208; 
x_206 = lean_ptr_addr(x_193);
lean_dec(x_193);
x_207 = lean_ptr_addr(x_187);
x_208 = lean_usize_dec_eq(x_206, x_207);
x_195 = x_208;
goto block_202;
}
block_202:
{
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; 
lean_dec(x_190);
x_196 = l_Lean_Expr_lam___override(x_191, x_184, x_187, x_182);
if (lean_is_scalar(x_189)) {
 x_197 = lean_alloc_ctor(0, 2, 0);
} else {
 x_197 = x_189;
}
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_188);
return x_197;
}
else
{
uint8_t x_198; 
x_198 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_194, x_182);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; 
lean_dec(x_190);
x_199 = l_Lean_Expr_lam___override(x_191, x_184, x_187, x_182);
if (lean_is_scalar(x_189)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_189;
}
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_188);
return x_200;
}
else
{
lean_object* x_201; 
lean_dec(x_191);
lean_dec(x_187);
lean_dec(x_184);
if (lean_is_scalar(x_189)) {
 x_201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_201 = x_189;
}
lean_ctor_set(x_201, 0, x_190);
lean_ctor_set(x_201, 1, x_188);
return x_201;
}
}
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_190);
lean_dec(x_187);
lean_dec(x_184);
x_209 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_210 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateLambda!Impl", 48, 48);
x_211 = lean_unsigned_to_nat(1848u);
x_212 = lean_unsigned_to_nat(19u);
x_213 = lean_mk_string_unchecked("lambda expected", 15, 15);
x_214 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_209, x_210, x_211, x_212, x_213);
lean_dec(x_213);
lean_dec(x_210);
lean_dec(x_209);
x_215 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_214);
if (lean_is_scalar(x_189)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_189;
}
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_188);
return x_216;
}
}
else
{
lean_dec(x_184);
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
return x_186;
}
}
else
{
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_183;
}
}
case 7:
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; lean_object* x_221; 
x_217 = lean_ctor_get(x_1, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_1, 1);
lean_inc(x_218);
x_219 = lean_ctor_get(x_1, 2);
lean_inc(x_219);
x_220 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_218);
x_221 = l_Lean_Meta_Closure_collectExprAux___lam__0(x_218, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
lean_inc(x_219);
x_224 = l_Lean_Meta_Closure_collectExprAux___lam__0(x_219, x_2, x_3, x_4, x_5, x_6, x_7, x_223);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_227 = x_224;
} else {
 lean_dec_ref(x_224);
 x_227 = lean_box(0);
}
x_228 = l_Lean_Expr_forallE___override(x_217, x_218, x_219, x_220);
if (lean_obj_tag(x_228) == 7)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; uint8_t x_233; size_t x_241; size_t x_242; uint8_t x_243; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
x_231 = lean_ctor_get(x_228, 2);
lean_inc(x_231);
x_232 = lean_ctor_get_uint8(x_228, sizeof(void*)*3 + 8);
x_241 = lean_ptr_addr(x_230);
lean_dec(x_230);
x_242 = lean_ptr_addr(x_222);
x_243 = lean_usize_dec_eq(x_241, x_242);
if (x_243 == 0)
{
lean_dec(x_231);
x_233 = x_243;
goto block_240;
}
else
{
size_t x_244; size_t x_245; uint8_t x_246; 
x_244 = lean_ptr_addr(x_231);
lean_dec(x_231);
x_245 = lean_ptr_addr(x_225);
x_246 = lean_usize_dec_eq(x_244, x_245);
x_233 = x_246;
goto block_240;
}
block_240:
{
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; 
lean_dec(x_228);
x_234 = l_Lean_Expr_forallE___override(x_229, x_222, x_225, x_220);
if (lean_is_scalar(x_227)) {
 x_235 = lean_alloc_ctor(0, 2, 0);
} else {
 x_235 = x_227;
}
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_226);
return x_235;
}
else
{
uint8_t x_236; 
x_236 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_232, x_220);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; 
lean_dec(x_228);
x_237 = l_Lean_Expr_forallE___override(x_229, x_222, x_225, x_220);
if (lean_is_scalar(x_227)) {
 x_238 = lean_alloc_ctor(0, 2, 0);
} else {
 x_238 = x_227;
}
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_226);
return x_238;
}
else
{
lean_object* x_239; 
lean_dec(x_229);
lean_dec(x_225);
lean_dec(x_222);
if (lean_is_scalar(x_227)) {
 x_239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_239 = x_227;
}
lean_ctor_set(x_239, 0, x_228);
lean_ctor_set(x_239, 1, x_226);
return x_239;
}
}
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_228);
lean_dec(x_225);
lean_dec(x_222);
x_247 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_248 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateForall!Impl", 48, 48);
x_249 = lean_unsigned_to_nat(1828u);
x_250 = lean_unsigned_to_nat(23u);
x_251 = lean_mk_string_unchecked("forall expected", 15, 15);
x_252 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_247, x_248, x_249, x_250, x_251);
lean_dec(x_251);
lean_dec(x_248);
lean_dec(x_247);
x_253 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_252);
if (lean_is_scalar(x_227)) {
 x_254 = lean_alloc_ctor(0, 2, 0);
} else {
 x_254 = x_227;
}
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_226);
return x_254;
}
}
else
{
lean_dec(x_222);
lean_dec(x_219);
lean_dec(x_218);
lean_dec(x_217);
return x_224;
}
}
else
{
lean_dec(x_219);
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_221;
}
}
case 8:
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; lean_object* x_260; 
x_255 = lean_ctor_get(x_1, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_1, 1);
lean_inc(x_256);
x_257 = lean_ctor_get(x_1, 2);
lean_inc(x_257);
x_258 = lean_ctor_get(x_1, 3);
lean_inc(x_258);
x_259 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_256);
x_260 = l_Lean_Meta_Closure_collectExprAux___lam__0(x_256, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_260, 1);
lean_inc(x_262);
lean_dec(x_260);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_257);
x_263 = l_Lean_Meta_Closure_collectExprAux___lam__0(x_257, x_2, x_3, x_4, x_5, x_6, x_7, x_262);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 x_266 = x_263;
} else {
 lean_dec_ref(x_263);
 x_266 = lean_box(0);
}
lean_inc(x_258);
x_267 = l_Lean_Meta_Closure_collectExprAux___lam__0(x_258, x_2, x_3, x_4, x_5, x_6, x_7, x_265);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_274; size_t x_280; size_t x_281; uint8_t x_282; 
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_267, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 x_270 = x_267;
} else {
 lean_dec_ref(x_267);
 x_270 = lean_box(0);
}
x_280 = lean_ptr_addr(x_256);
lean_dec(x_256);
x_281 = lean_ptr_addr(x_261);
x_282 = lean_usize_dec_eq(x_280, x_281);
if (x_282 == 0)
{
lean_dec(x_257);
x_274 = x_282;
goto block_279;
}
else
{
size_t x_283; size_t x_284; uint8_t x_285; 
x_283 = lean_ptr_addr(x_257);
lean_dec(x_257);
x_284 = lean_ptr_addr(x_264);
x_285 = lean_usize_dec_eq(x_283, x_284);
x_274 = x_285;
goto block_279;
}
block_273:
{
lean_object* x_271; lean_object* x_272; 
x_271 = l_Lean_Expr_letE___override(x_255, x_261, x_264, x_268, x_259);
if (lean_is_scalar(x_270)) {
 x_272 = lean_alloc_ctor(0, 2, 0);
} else {
 x_272 = x_270;
}
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_269);
return x_272;
}
block_279:
{
if (x_274 == 0)
{
lean_dec(x_266);
lean_dec(x_258);
lean_dec(x_1);
goto block_273;
}
else
{
size_t x_275; size_t x_276; uint8_t x_277; 
x_275 = lean_ptr_addr(x_258);
lean_dec(x_258);
x_276 = lean_ptr_addr(x_268);
x_277 = lean_usize_dec_eq(x_275, x_276);
if (x_277 == 0)
{
lean_dec(x_266);
lean_dec(x_1);
goto block_273;
}
else
{
lean_object* x_278; 
lean_dec(x_270);
lean_dec(x_268);
lean_dec(x_264);
lean_dec(x_261);
lean_dec(x_255);
if (lean_is_scalar(x_266)) {
 x_278 = lean_alloc_ctor(0, 2, 0);
} else {
 x_278 = x_266;
}
lean_ctor_set(x_278, 0, x_1);
lean_ctor_set(x_278, 1, x_269);
return x_278;
}
}
}
}
else
{
lean_dec(x_266);
lean_dec(x_264);
lean_dec(x_261);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_1);
return x_267;
}
}
else
{
lean_dec(x_261);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_263;
}
}
else
{
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_260;
}
}
case 10:
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_1, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_1, 1);
lean_inc(x_287);
lean_inc(x_287);
x_288 = l_Lean_Meta_Closure_collectExprAux___lam__0(x_287, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_288) == 0)
{
uint8_t x_289; 
x_289 = !lean_is_exclusive(x_288);
if (x_289 == 0)
{
lean_object* x_290; size_t x_291; size_t x_292; uint8_t x_293; 
x_290 = lean_ctor_get(x_288, 0);
x_291 = lean_ptr_addr(x_287);
lean_dec(x_287);
x_292 = lean_ptr_addr(x_290);
x_293 = lean_usize_dec_eq(x_291, x_292);
if (x_293 == 0)
{
lean_object* x_294; 
lean_dec(x_1);
x_294 = l_Lean_Expr_mdata___override(x_286, x_290);
lean_ctor_set(x_288, 0, x_294);
return x_288;
}
else
{
lean_dec(x_290);
lean_dec(x_286);
lean_ctor_set(x_288, 0, x_1);
return x_288;
}
}
else
{
lean_object* x_295; lean_object* x_296; size_t x_297; size_t x_298; uint8_t x_299; 
x_295 = lean_ctor_get(x_288, 0);
x_296 = lean_ctor_get(x_288, 1);
lean_inc(x_296);
lean_inc(x_295);
lean_dec(x_288);
x_297 = lean_ptr_addr(x_287);
lean_dec(x_287);
x_298 = lean_ptr_addr(x_295);
x_299 = lean_usize_dec_eq(x_297, x_298);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; 
lean_dec(x_1);
x_300 = l_Lean_Expr_mdata___override(x_286, x_295);
x_301 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_296);
return x_301;
}
else
{
lean_object* x_302; 
lean_dec(x_295);
lean_dec(x_286);
x_302 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_302, 0, x_1);
lean_ctor_set(x_302, 1, x_296);
return x_302;
}
}
}
else
{
lean_dec(x_287);
lean_dec(x_286);
lean_dec(x_1);
return x_288;
}
}
case 11:
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_303 = lean_ctor_get(x_1, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_1, 1);
lean_inc(x_304);
x_305 = lean_ctor_get(x_1, 2);
lean_inc(x_305);
lean_inc(x_305);
x_306 = l_Lean_Meta_Closure_collectExprAux___lam__0(x_305, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_306) == 0)
{
uint8_t x_307; 
x_307 = !lean_is_exclusive(x_306);
if (x_307 == 0)
{
lean_object* x_308; size_t x_309; size_t x_310; uint8_t x_311; 
x_308 = lean_ctor_get(x_306, 0);
x_309 = lean_ptr_addr(x_305);
lean_dec(x_305);
x_310 = lean_ptr_addr(x_308);
x_311 = lean_usize_dec_eq(x_309, x_310);
if (x_311 == 0)
{
lean_object* x_312; 
lean_dec(x_1);
x_312 = l_Lean_Expr_proj___override(x_303, x_304, x_308);
lean_ctor_set(x_306, 0, x_312);
return x_306;
}
else
{
lean_dec(x_308);
lean_dec(x_304);
lean_dec(x_303);
lean_ctor_set(x_306, 0, x_1);
return x_306;
}
}
else
{
lean_object* x_313; lean_object* x_314; size_t x_315; size_t x_316; uint8_t x_317; 
x_313 = lean_ctor_get(x_306, 0);
x_314 = lean_ctor_get(x_306, 1);
lean_inc(x_314);
lean_inc(x_313);
lean_dec(x_306);
x_315 = lean_ptr_addr(x_305);
lean_dec(x_305);
x_316 = lean_ptr_addr(x_313);
x_317 = lean_usize_dec_eq(x_315, x_316);
if (x_317 == 0)
{
lean_object* x_318; lean_object* x_319; 
lean_dec(x_1);
x_318 = l_Lean_Expr_proj___override(x_303, x_304, x_313);
x_319 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_319, 1, x_314);
return x_319;
}
else
{
lean_object* x_320; 
lean_dec(x_313);
lean_dec(x_304);
lean_dec(x_303);
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_1);
lean_ctor_set(x_320, 1, x_314);
return x_320;
}
}
}
else
{
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_1);
return x_306;
}
}
default: 
{
lean_object* x_321; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_321 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_321, 0, x_1);
lean_ctor_set(x_321, 1, x_8);
return x_321;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Meta_Closure_collectExprAux_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Meta_Closure_collectExprAux_spec__0_spec__0(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___Lean_Meta_Closure_collectExprAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_mkFreshFVarId___at___Lean_Meta_Closure_collectExprAux_spec__0(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___Lean_Meta_Closure_collectExprAux_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getDelayedMVarAssignment_x3f___at___Lean_Meta_Closure_collectExprAux_spec__2___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___Lean_Meta_Closure_collectExprAux_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_getDelayedMVarAssignment_x3f___at___Lean_Meta_Closure_collectExprAux_spec__2(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_Closure_collectExprAux_spec__3___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_Closure_collectExprAux_spec__3___redArg___lam__0(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_Closure_collectExprAux_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_Closure_collectExprAux_spec__3___redArg(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_Closure_collectExprAux_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = lean_unbox(x_6);
lean_dec(x_6);
x_15 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_Closure_collectExprAux_spec__3(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_Closure_collectExprAux_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_mapM_loop___at___Lean_Meta_Closure_collectExprAux_spec__4___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_Closure_collectExprAux_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_List_mapM_loop___at___Lean_Meta_Closure_collectExprAux_spec__4(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_Closure_collectExprAux___lam__0(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_Meta_Closure_collectExprAux___lam__1(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_Closure_collectExprAux(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_31; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_31 = l_Lean_Meta_Closure_preprocess(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_174; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
x_174 = l_Lean_Expr_hasLevelParam(x_32);
if (x_174 == 0)
{
uint8_t x_175; 
x_175 = l_Lean_Expr_hasFVar(x_32);
if (x_175 == 0)
{
uint8_t x_176; 
x_176 = l_Lean_Expr_hasMVar(x_32);
if (x_176 == 0)
{
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_31;
}
else
{
lean_dec(x_31);
goto block_173;
}
}
else
{
lean_dec(x_31);
goto block_173;
}
}
else
{
lean_dec(x_31);
goto block_173;
}
block_173:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_st_ref_get(x_3, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint64_t x_42; lean_object* x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; lean_object* x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; size_t x_51; size_t x_52; lean_object* x_53; size_t x_54; size_t x_55; size_t x_56; lean_object* x_57; lean_object* x_58; 
x_38 = lean_ctor_get(x_34, 1);
x_39 = lean_ctor_get(x_34, 0);
lean_dec(x_39);
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_dec(x_36);
x_41 = lean_array_get_size(x_40);
x_42 = l_Lean_Expr_hash(x_32);
x_43 = lean_unsigned_to_nat(32u);
x_44 = lean_uint64_of_nat(x_43);
x_45 = lean_uint64_shift_right(x_42, x_44);
x_46 = lean_uint64_xor(x_42, x_45);
x_47 = lean_unsigned_to_nat(16u);
x_48 = lean_uint64_of_nat(x_47);
x_49 = lean_uint64_shift_right(x_46, x_48);
x_50 = lean_uint64_xor(x_46, x_49);
x_51 = lean_uint64_to_usize(x_50);
x_52 = lean_usize_of_nat(x_41);
lean_dec(x_41);
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_usize_of_nat(x_53);
x_55 = lean_usize_sub(x_52, x_54);
x_56 = lean_usize_land(x_51, x_55);
x_57 = lean_array_uget(x_40, x_56);
lean_dec(x_40);
x_58 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__0(lean_box(0), x_32, x_57);
lean_dec(x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
lean_free_object(x_34);
lean_inc(x_3);
lean_inc(x_32);
x_59 = l_Lean_Meta_Closure_collectExprAux(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_38);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_st_ref_take(x_3, x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = !lean_is_exclusive(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; size_t x_71; size_t x_72; size_t x_73; lean_object* x_74; uint8_t x_75; 
x_67 = lean_ctor_get(x_64, 0);
x_68 = lean_ctor_get(x_64, 1);
x_69 = lean_ctor_get(x_63, 0);
lean_inc(x_69);
x_70 = lean_array_get_size(x_68);
x_71 = lean_usize_of_nat(x_70);
lean_dec(x_70);
x_72 = lean_usize_sub(x_71, x_54);
x_73 = lean_usize_land(x_51, x_72);
x_74 = lean_array_uget(x_68, x_73);
x_75 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__1(lean_box(0), x_32, x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_76 = lean_nat_add(x_67, x_53);
lean_dec(x_67);
lean_inc(x_60);
x_77 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_77, 0, x_32);
lean_ctor_set(x_77, 1, x_60);
lean_ctor_set(x_77, 2, x_74);
x_78 = lean_array_uset(x_68, x_73, x_77);
x_79 = lean_unsigned_to_nat(2u);
x_80 = lean_nat_shiftl(x_76, x_79);
x_81 = lean_unsigned_to_nat(3u);
x_82 = lean_nat_div(x_80, x_81);
lean_dec(x_80);
x_83 = lean_array_get_size(x_78);
x_84 = lean_nat_dec_le(x_82, x_83);
lean_dec(x_83);
lean_dec(x_82);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2(lean_box(0), x_78);
lean_ctor_set(x_64, 1, x_85);
lean_ctor_set(x_64, 0, x_76);
x_9 = x_65;
x_10 = x_69;
x_11 = x_60;
x_12 = x_63;
x_13 = x_64;
goto block_30;
}
else
{
lean_ctor_set(x_64, 1, x_78);
lean_ctor_set(x_64, 0, x_76);
x_9 = x_65;
x_10 = x_69;
x_11 = x_60;
x_12 = x_63;
x_13 = x_64;
goto block_30;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_box(0);
x_87 = lean_array_uset(x_68, x_73, x_86);
lean_inc(x_60);
x_88 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__5(lean_box(0), x_32, x_60, x_74);
x_89 = lean_array_uset(x_87, x_73, x_88);
lean_ctor_set(x_64, 1, x_89);
x_9 = x_65;
x_10 = x_69;
x_11 = x_60;
x_12 = x_63;
x_13 = x_64;
goto block_30;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; size_t x_94; size_t x_95; size_t x_96; lean_object* x_97; uint8_t x_98; 
x_90 = lean_ctor_get(x_64, 0);
x_91 = lean_ctor_get(x_64, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_64);
x_92 = lean_ctor_get(x_63, 0);
lean_inc(x_92);
x_93 = lean_array_get_size(x_91);
x_94 = lean_usize_of_nat(x_93);
lean_dec(x_93);
x_95 = lean_usize_sub(x_94, x_54);
x_96 = lean_usize_land(x_51, x_95);
x_97 = lean_array_uget(x_91, x_96);
x_98 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__1(lean_box(0), x_32, x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_99 = lean_nat_add(x_90, x_53);
lean_dec(x_90);
lean_inc(x_60);
x_100 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_100, 0, x_32);
lean_ctor_set(x_100, 1, x_60);
lean_ctor_set(x_100, 2, x_97);
x_101 = lean_array_uset(x_91, x_96, x_100);
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
x_108 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2(lean_box(0), x_101);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_99);
lean_ctor_set(x_109, 1, x_108);
x_9 = x_65;
x_10 = x_92;
x_11 = x_60;
x_12 = x_63;
x_13 = x_109;
goto block_30;
}
else
{
lean_object* x_110; 
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_99);
lean_ctor_set(x_110, 1, x_101);
x_9 = x_65;
x_10 = x_92;
x_11 = x_60;
x_12 = x_63;
x_13 = x_110;
goto block_30;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_111 = lean_box(0);
x_112 = lean_array_uset(x_91, x_96, x_111);
lean_inc(x_60);
x_113 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__5(lean_box(0), x_32, x_60, x_97);
x_114 = lean_array_uset(x_112, x_96, x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_90);
lean_ctor_set(x_115, 1, x_114);
x_9 = x_65;
x_10 = x_92;
x_11 = x_60;
x_12 = x_63;
x_13 = x_115;
goto block_30;
}
}
}
else
{
lean_dec(x_32);
lean_dec(x_3);
return x_59;
}
}
else
{
lean_object* x_116; 
lean_dec(x_32);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_116 = lean_ctor_get(x_58, 0);
lean_inc(x_116);
lean_dec(x_58);
lean_ctor_set(x_34, 0, x_116);
return x_34;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; uint64_t x_120; lean_object* x_121; uint64_t x_122; uint64_t x_123; uint64_t x_124; lean_object* x_125; uint64_t x_126; uint64_t x_127; uint64_t x_128; size_t x_129; size_t x_130; lean_object* x_131; size_t x_132; size_t x_133; size_t x_134; lean_object* x_135; lean_object* x_136; 
x_117 = lean_ctor_get(x_34, 1);
lean_inc(x_117);
lean_dec(x_34);
x_118 = lean_ctor_get(x_36, 1);
lean_inc(x_118);
lean_dec(x_36);
x_119 = lean_array_get_size(x_118);
x_120 = l_Lean_Expr_hash(x_32);
x_121 = lean_unsigned_to_nat(32u);
x_122 = lean_uint64_of_nat(x_121);
x_123 = lean_uint64_shift_right(x_120, x_122);
x_124 = lean_uint64_xor(x_120, x_123);
x_125 = lean_unsigned_to_nat(16u);
x_126 = lean_uint64_of_nat(x_125);
x_127 = lean_uint64_shift_right(x_124, x_126);
x_128 = lean_uint64_xor(x_124, x_127);
x_129 = lean_uint64_to_usize(x_128);
x_130 = lean_usize_of_nat(x_119);
lean_dec(x_119);
x_131 = lean_unsigned_to_nat(1u);
x_132 = lean_usize_of_nat(x_131);
x_133 = lean_usize_sub(x_130, x_132);
x_134 = lean_usize_land(x_129, x_133);
x_135 = lean_array_uget(x_118, x_134);
lean_dec(x_118);
x_136 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__0(lean_box(0), x_32, x_135);
lean_dec(x_135);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; 
lean_inc(x_3);
lean_inc(x_32);
x_137 = l_Lean_Meta_Closure_collectExprAux(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_117);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; size_t x_149; size_t x_150; size_t x_151; lean_object* x_152; uint8_t x_153; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_140 = lean_st_ref_take(x_3, x_139);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_140, 1);
lean_inc(x_143);
lean_dec(x_140);
x_144 = lean_ctor_get(x_142, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_146 = x_142;
} else {
 lean_dec_ref(x_142);
 x_146 = lean_box(0);
}
x_147 = lean_ctor_get(x_141, 0);
lean_inc(x_147);
x_148 = lean_array_get_size(x_145);
x_149 = lean_usize_of_nat(x_148);
lean_dec(x_148);
x_150 = lean_usize_sub(x_149, x_132);
x_151 = lean_usize_land(x_129, x_150);
x_152 = lean_array_uget(x_145, x_151);
x_153 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__1(lean_box(0), x_32, x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_154 = lean_nat_add(x_144, x_131);
lean_dec(x_144);
lean_inc(x_138);
x_155 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_155, 0, x_32);
lean_ctor_set(x_155, 1, x_138);
lean_ctor_set(x_155, 2, x_152);
x_156 = lean_array_uset(x_145, x_151, x_155);
x_157 = lean_unsigned_to_nat(2u);
x_158 = lean_nat_shiftl(x_154, x_157);
x_159 = lean_unsigned_to_nat(3u);
x_160 = lean_nat_div(x_158, x_159);
lean_dec(x_158);
x_161 = lean_array_get_size(x_156);
x_162 = lean_nat_dec_le(x_160, x_161);
lean_dec(x_161);
lean_dec(x_160);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; 
x_163 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2(lean_box(0), x_156);
if (lean_is_scalar(x_146)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_146;
}
lean_ctor_set(x_164, 0, x_154);
lean_ctor_set(x_164, 1, x_163);
x_9 = x_143;
x_10 = x_147;
x_11 = x_138;
x_12 = x_141;
x_13 = x_164;
goto block_30;
}
else
{
lean_object* x_165; 
if (lean_is_scalar(x_146)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_146;
}
lean_ctor_set(x_165, 0, x_154);
lean_ctor_set(x_165, 1, x_156);
x_9 = x_143;
x_10 = x_147;
x_11 = x_138;
x_12 = x_141;
x_13 = x_165;
goto block_30;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_166 = lean_box(0);
x_167 = lean_array_uset(x_145, x_151, x_166);
lean_inc(x_138);
x_168 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__5(lean_box(0), x_32, x_138, x_152);
x_169 = lean_array_uset(x_167, x_151, x_168);
if (lean_is_scalar(x_146)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_146;
}
lean_ctor_set(x_170, 0, x_144);
lean_ctor_set(x_170, 1, x_169);
x_9 = x_143;
x_10 = x_147;
x_11 = x_138;
x_12 = x_141;
x_13 = x_170;
goto block_30;
}
}
else
{
lean_dec(x_32);
lean_dec(x_3);
return x_137;
}
}
else
{
lean_object* x_171; lean_object* x_172; 
lean_dec(x_32);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_171 = lean_ctor_get(x_136, 0);
lean_inc(x_171);
lean_dec(x_136);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_117);
return x_172;
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
lean_dec(x_3);
return x_31;
}
block_30:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_14 = lean_ctor_get(x_12, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 4);
lean_inc(x_16);
x_17 = lean_ctor_get(x_12, 5);
lean_inc(x_17);
x_18 = lean_ctor_get(x_12, 6);
lean_inc(x_18);
x_19 = lean_ctor_get(x_12, 7);
lean_inc(x_19);
x_20 = lean_ctor_get(x_12, 8);
lean_inc(x_20);
x_21 = lean_ctor_get(x_12, 9);
lean_inc(x_21);
x_22 = lean_ctor_get(x_12, 10);
lean_inc(x_22);
x_23 = lean_ctor_get(x_12, 11);
lean_inc(x_23);
lean_dec(x_12);
x_24 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_24, 0, x_10);
lean_ctor_set(x_24, 1, x_13);
lean_ctor_set(x_24, 2, x_14);
lean_ctor_set(x_24, 3, x_15);
lean_ctor_set(x_24, 4, x_16);
lean_ctor_set(x_24, 5, x_17);
lean_ctor_set(x_24, 6, x_18);
lean_ctor_set(x_24, 7, x_19);
lean_ctor_set(x_24, 8, x_20);
lean_ctor_set(x_24, 9, x_21);
lean_ctor_set(x_24, 10, x_22);
lean_ctor_set(x_24, 11, x_23);
x_25 = lean_st_ref_set(x_3, x_24, x_9);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_11);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_11);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_Closure_collectExpr(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcessAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_3);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_20; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_8 = lean_array_fget(x_3, x_2);
x_25 = lean_ctor_get(x_4, 0);
lean_inc(x_25);
lean_inc(x_1);
x_26 = l_Lean_LocalContext_get_x21(x_1, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_20 = x_27;
goto block_24;
block_19:
{
uint8_t x_11; 
x_11 = lean_nat_dec_lt(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
lean_dec(x_2);
x_2 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_2, x_15);
x_17 = lean_array_fset(x_3, x_2, x_4);
lean_dec(x_2);
x_2 = x_16;
x_3 = x_17;
x_4 = x_8;
goto _start;
}
}
block_24:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_8, 0);
lean_inc(x_21);
lean_inc(x_1);
x_22 = l_Lean_LocalContext_get_x21(x_1, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_9 = x_20;
x_10 = x_23;
goto block_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_1, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_6, 11);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Array_isEmpty___redArg(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_free_object(x_4);
x_10 = lean_st_ref_take(x_1, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_Lean_Meta_Closure_instInhabitedToProcessElement;
x_15 = lean_ctor_get(x_11, 11);
lean_inc(x_15);
x_16 = l_Array_back_x21(lean_box(0), x_14, x_15);
x_17 = lean_array_pop(x_15);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Meta_Closure_pickNextToProcessAux(x_13, x_18, x_17, x_16);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_11, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_11, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_11, 3);
lean_inc(x_25);
x_26 = lean_ctor_get(x_11, 4);
lean_inc(x_26);
x_27 = lean_ctor_get(x_11, 5);
lean_inc(x_27);
x_28 = lean_ctor_get(x_11, 6);
lean_inc(x_28);
x_29 = lean_ctor_get(x_11, 7);
lean_inc(x_29);
x_30 = lean_ctor_get(x_11, 8);
lean_inc(x_30);
x_31 = lean_ctor_get(x_11, 9);
lean_inc(x_31);
x_32 = lean_ctor_get(x_11, 10);
lean_inc(x_32);
lean_dec(x_11);
x_33 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_33, 0, x_22);
lean_ctor_set(x_33, 1, x_23);
lean_ctor_set(x_33, 2, x_24);
lean_ctor_set(x_33, 3, x_25);
lean_ctor_set(x_33, 4, x_26);
lean_ctor_set(x_33, 5, x_27);
lean_ctor_set(x_33, 6, x_28);
lean_ctor_set(x_33, 7, x_29);
lean_ctor_set(x_33, 8, x_30);
lean_ctor_set(x_33, 9, x_31);
lean_ctor_set(x_33, 10, x_32);
lean_ctor_set(x_33, 11, x_21);
x_34 = lean_st_ref_set(x_1, x_33, x_12);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_20);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_20);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
lean_object* x_41; 
lean_dec(x_2);
x_41 = lean_box(0);
lean_ctor_set(x_4, 0, x_41);
return x_4;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_4, 0);
x_43 = lean_ctor_get(x_4, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_4);
x_44 = lean_ctor_get(x_42, 11);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Array_isEmpty___redArg(x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_46 = lean_st_ref_take(x_1, x_43);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_ctor_get(x_2, 2);
lean_inc(x_49);
lean_dec(x_2);
x_50 = l_Lean_Meta_Closure_instInhabitedToProcessElement;
x_51 = lean_ctor_get(x_47, 11);
lean_inc(x_51);
x_52 = l_Array_back_x21(lean_box(0), x_50, x_51);
x_53 = lean_array_pop(x_51);
x_54 = lean_unsigned_to_nat(0u);
x_55 = l_Lean_Meta_Closure_pickNextToProcessAux(x_49, x_54, x_53, x_52);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_ctor_get(x_47, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_47, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_47, 2);
lean_inc(x_60);
x_61 = lean_ctor_get(x_47, 3);
lean_inc(x_61);
x_62 = lean_ctor_get(x_47, 4);
lean_inc(x_62);
x_63 = lean_ctor_get(x_47, 5);
lean_inc(x_63);
x_64 = lean_ctor_get(x_47, 6);
lean_inc(x_64);
x_65 = lean_ctor_get(x_47, 7);
lean_inc(x_65);
x_66 = lean_ctor_get(x_47, 8);
lean_inc(x_66);
x_67 = lean_ctor_get(x_47, 9);
lean_inc(x_67);
x_68 = lean_ctor_get(x_47, 10);
lean_inc(x_68);
lean_dec(x_47);
x_69 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_69, 0, x_58);
lean_ctor_set(x_69, 1, x_59);
lean_ctor_set(x_69, 2, x_60);
lean_ctor_set(x_69, 3, x_61);
lean_ctor_set(x_69, 4, x_62);
lean_ctor_set(x_69, 5, x_63);
lean_ctor_set(x_69, 6, x_64);
lean_ctor_set(x_69, 7, x_65);
lean_ctor_set(x_69, 8, x_66);
lean_ctor_set(x_69, 9, x_67);
lean_ctor_set(x_69, 10, x_68);
lean_ctor_set(x_69, 11, x_57);
x_70 = lean_st_ref_set(x_1, x_69, x_48);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_72 = x_70;
} else {
 lean_dec_ref(x_70);
 x_72 = lean_box(0);
}
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_56);
if (lean_is_scalar(x_72)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_72;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_2);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_43);
return x_76;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(x_2, x_3, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_Meta_Closure_pickNextToProcess_x3f(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
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
x_15 = lean_ctor_get(x_5, 8);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 9);
lean_inc(x_16);
x_17 = lean_ctor_get(x_5, 10);
lean_inc(x_17);
x_18 = lean_array_push(x_17, x_1);
x_19 = lean_ctor_get(x_5, 11);
lean_inc(x_19);
lean_dec(x_5);
x_20 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_8);
lean_ctor_set(x_20, 2, x_9);
lean_ctor_set(x_20, 3, x_10);
lean_ctor_set(x_20, 4, x_11);
lean_ctor_set(x_20, 5, x_12);
lean_ctor_set(x_20, 6, x_13);
lean_ctor_set(x_20, 7, x_14);
lean_ctor_set(x_20, 8, x_15);
lean_ctor_set(x_20, 9, x_16);
lean_ctor_set(x_20, 10, x_18);
lean_ctor_set(x_20, 11, x_19);
x_21 = lean_st_ref_set(x_2, x_20, x_6);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Closure_pushFVarArg___redArg(x_1, x_3, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Closure_pushFVarArg___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_Closure_pushFVarArg(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_6);
x_12 = l_Lean_Meta_Closure_collectExpr(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_take(x_6, x_14);
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
x_23 = lean_ctor_get(x_16, 5);
lean_inc(x_23);
x_24 = lean_box(0);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_1);
lean_ctor_set(x_26, 2, x_2);
lean_ctor_set(x_26, 3, x_13);
lean_ctor_set_uint8(x_26, sizeof(void*)*4, x_4);
x_27 = lean_unbox(x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*4 + 1, x_27);
x_28 = lean_array_push(x_23, x_26);
x_29 = lean_ctor_get(x_16, 6);
lean_inc(x_29);
x_30 = lean_ctor_get(x_16, 7);
lean_inc(x_30);
x_31 = lean_ctor_get(x_16, 8);
lean_inc(x_31);
x_32 = lean_ctor_get(x_16, 9);
lean_inc(x_32);
x_33 = lean_ctor_get(x_16, 10);
lean_inc(x_33);
x_34 = lean_ctor_get(x_16, 11);
lean_inc(x_34);
lean_dec(x_16);
x_35 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_35, 0, x_18);
lean_ctor_set(x_35, 1, x_19);
lean_ctor_set(x_35, 2, x_20);
lean_ctor_set(x_35, 3, x_21);
lean_ctor_set(x_35, 4, x_22);
lean_ctor_set(x_35, 5, x_28);
lean_ctor_set(x_35, 6, x_29);
lean_ctor_set(x_35, 7, x_30);
lean_ctor_set(x_35, 8, x_31);
lean_ctor_set(x_35, 9, x_32);
lean_ctor_set(x_35, 10, x_33);
lean_ctor_set(x_35, 11, x_34);
x_36 = lean_st_ref_set(x_6, x_35, x_17);
lean_dec(x_6);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
x_39 = lean_box(0);
lean_ctor_set(x_36, 0, x_39);
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_dec(x_36);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_12);
if (x_43 == 0)
{
return x_12;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_12, 0);
x_45 = lean_ctor_get(x_12, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_12);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l_Lean_Meta_Closure_pushLocalDecl(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___Lean_Meta_Closure_process_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickCmp(x_2, x_5);
switch (x_8) {
case 0:
{
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_6);
lean_inc(x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
default: 
{
x_1 = x_7;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___Lean_Meta_Closure_process_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_findCore___at___Lean_Meta_Closure_process_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Closure_process_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_7 = lean_array_uget(x_5, x_4);
x_8 = lean_box(0);
x_9 = lean_array_uset(x_5, x_4, x_8);
lean_inc(x_1);
x_10 = l_Lean_LocalDecl_replaceFVarId(x_1, x_2, x_7);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_3);
x_8 = l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(x_2, x_3, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
lean_inc(x_3);
lean_inc(x_18);
x_20 = l_Lean_FVarId_getDecl___redArg(x_18, x_3, x_5, x_6, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 3);
lean_inc(x_24);
x_25 = lean_ctor_get_uint8(x_21, sizeof(void*)*4);
lean_dec(x_21);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_26 = l_Lean_Meta_Closure_pushLocalDecl(x_19, x_23, x_24, x_25, x_1, x_2, x_3, x_4, x_5, x_6, x_22);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_Expr_fvar___override(x_18);
x_29 = l_Lean_Meta_Closure_pushFVarArg___redArg(x_28, x_2, x_27);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_7 = x_30;
goto _start;
}
else
{
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_26;
}
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_dec(x_20);
x_33 = !lean_is_exclusive(x_21);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_34 = lean_ctor_get(x_21, 2);
x_35 = lean_ctor_get(x_21, 3);
x_36 = lean_ctor_get(x_21, 4);
x_37 = lean_ctor_get(x_21, 1);
lean_dec(x_37);
x_38 = lean_ctor_get(x_21, 0);
lean_dec(x_38);
x_39 = l_Lean_Meta_getZetaDeltaFVarIds(x_3, x_4, x_5, x_6, x_32);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_RBNode_findCore___at___Lean_Meta_Closure_process_spec__0___redArg(x_40, x_18);
lean_dec(x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; uint8_t x_44; lean_object* x_45; 
lean_free_object(x_21);
lean_dec(x_36);
x_43 = lean_box(0);
x_44 = lean_unbox(x_43);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_45 = l_Lean_Meta_Closure_pushLocalDecl(x_19, x_34, x_35, x_44, x_1, x_2, x_3, x_4, x_5, x_6, x_41);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_Lean_Expr_fvar___override(x_18);
x_48 = l_Lean_Meta_Closure_pushFVarArg___redArg(x_47, x_2, x_46);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_7 = x_49;
goto _start;
}
else
{
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_45;
}
}
else
{
lean_object* x_51; 
lean_dec(x_42);
lean_dec(x_18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_51 = l_Lean_Meta_Closure_collectExpr(x_35, x_1, x_2, x_3, x_4, x_5, x_6, x_41);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_54 = l_Lean_Meta_Closure_collectExpr(x_36, x_1, x_2, x_3, x_4, x_5, x_6, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; size_t x_90; lean_object* x_91; size_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_st_ref_take(x_2, x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_box(0);
x_61 = lean_ctor_get(x_58, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_58, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_58, 2);
lean_inc(x_63);
x_64 = lean_ctor_get(x_58, 3);
lean_inc(x_64);
x_65 = lean_ctor_get(x_58, 4);
lean_inc(x_65);
x_66 = lean_ctor_get(x_58, 5);
lean_inc(x_66);
x_67 = lean_ctor_get(x_58, 6);
lean_inc(x_67);
x_68 = lean_ctor_get(x_58, 7);
lean_inc(x_68);
x_69 = lean_box(0);
x_70 = lean_box(0);
lean_inc(x_55);
lean_inc(x_19);
lean_ctor_set(x_21, 4, x_55);
lean_ctor_set(x_21, 3, x_52);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 0, x_69);
x_71 = lean_unbox(x_60);
lean_ctor_set_uint8(x_21, sizeof(void*)*5, x_71);
x_72 = lean_unbox(x_70);
lean_ctor_set_uint8(x_21, sizeof(void*)*5 + 1, x_72);
x_73 = lean_array_push(x_68, x_21);
x_74 = lean_ctor_get(x_58, 8);
lean_inc(x_74);
x_75 = lean_ctor_get(x_58, 9);
lean_inc(x_75);
x_76 = lean_ctor_get(x_58, 10);
lean_inc(x_76);
x_77 = lean_ctor_get(x_58, 11);
lean_inc(x_77);
lean_dec(x_58);
x_78 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_78, 0, x_61);
lean_ctor_set(x_78, 1, x_62);
lean_ctor_set(x_78, 2, x_63);
lean_ctor_set(x_78, 3, x_64);
lean_ctor_set(x_78, 4, x_65);
lean_ctor_set(x_78, 5, x_66);
lean_ctor_set(x_78, 6, x_67);
lean_ctor_set(x_78, 7, x_73);
lean_ctor_set(x_78, 8, x_74);
lean_ctor_set(x_78, 9, x_75);
lean_ctor_set(x_78, 10, x_76);
lean_ctor_set(x_78, 11, x_77);
x_79 = lean_st_ref_set(x_2, x_78, x_59);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = lean_st_ref_take(x_2, x_80);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_ctor_get(x_82, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_82, 2);
lean_inc(x_86);
x_87 = lean_ctor_get(x_82, 3);
lean_inc(x_87);
x_88 = lean_ctor_get(x_82, 4);
lean_inc(x_88);
x_89 = lean_ctor_get(x_82, 5);
lean_inc(x_89);
x_90 = lean_array_size(x_89);
x_91 = lean_unsigned_to_nat(0u);
x_92 = lean_usize_of_nat(x_91);
x_93 = l_Array_mapMUnsafe_map___at___Lean_Meta_Closure_process_spec__1(x_19, x_55, x_90, x_92, x_89);
lean_dec(x_55);
x_94 = lean_ctor_get(x_82, 6);
lean_inc(x_94);
x_95 = lean_ctor_get(x_82, 7);
lean_inc(x_95);
x_96 = lean_ctor_get(x_82, 8);
lean_inc(x_96);
x_97 = lean_ctor_get(x_82, 9);
lean_inc(x_97);
x_98 = lean_ctor_get(x_82, 10);
lean_inc(x_98);
x_99 = lean_ctor_get(x_82, 11);
lean_inc(x_99);
lean_dec(x_82);
x_100 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_100, 0, x_84);
lean_ctor_set(x_100, 1, x_85);
lean_ctor_set(x_100, 2, x_86);
lean_ctor_set(x_100, 3, x_87);
lean_ctor_set(x_100, 4, x_88);
lean_ctor_set(x_100, 5, x_93);
lean_ctor_set(x_100, 6, x_94);
lean_ctor_set(x_100, 7, x_95);
lean_ctor_set(x_100, 8, x_96);
lean_ctor_set(x_100, 9, x_97);
lean_ctor_set(x_100, 10, x_98);
lean_ctor_set(x_100, 11, x_99);
x_101 = lean_st_ref_set(x_2, x_100, x_83);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
x_7 = x_102;
goto _start;
}
else
{
uint8_t x_104; 
lean_dec(x_52);
lean_free_object(x_21);
lean_dec(x_34);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_104 = !lean_is_exclusive(x_54);
if (x_104 == 0)
{
return x_54;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_54, 0);
x_106 = lean_ctor_get(x_54, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_54);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
uint8_t x_108; 
lean_free_object(x_21);
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_108 = !lean_is_exclusive(x_51);
if (x_108 == 0)
{
return x_51;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_51, 0);
x_110 = lean_ctor_get(x_51, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_51);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_112 = lean_ctor_get(x_21, 2);
x_113 = lean_ctor_get(x_21, 3);
x_114 = lean_ctor_get(x_21, 4);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_21);
x_115 = l_Lean_Meta_getZetaDeltaFVarIds(x_3, x_4, x_5, x_6, x_32);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = l_Lean_RBNode_findCore___at___Lean_Meta_Closure_process_spec__0___redArg(x_116, x_18);
lean_dec(x_116);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; uint8_t x_120; lean_object* x_121; 
lean_dec(x_114);
x_119 = lean_box(0);
x_120 = lean_unbox(x_119);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_121 = l_Lean_Meta_Closure_pushLocalDecl(x_19, x_112, x_113, x_120, x_1, x_2, x_3, x_4, x_5, x_6, x_117);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
lean_dec(x_121);
x_123 = l_Lean_Expr_fvar___override(x_18);
x_124 = l_Lean_Meta_Closure_pushFVarArg___redArg(x_123, x_2, x_122);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
lean_dec(x_124);
x_7 = x_125;
goto _start;
}
else
{
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_121;
}
}
else
{
lean_object* x_127; 
lean_dec(x_118);
lean_dec(x_18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_127 = l_Lean_Meta_Closure_collectExpr(x_113, x_1, x_2, x_3, x_4, x_5, x_6, x_117);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_130 = l_Lean_Meta_Closure_collectExpr(x_114, x_1, x_2, x_3, x_4, x_5, x_6, x_129);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; uint8_t x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; size_t x_167; lean_object* x_168; size_t x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_st_ref_take(x_2, x_132);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_box(0);
x_137 = lean_ctor_get(x_134, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_134, 1);
lean_inc(x_138);
x_139 = lean_ctor_get(x_134, 2);
lean_inc(x_139);
x_140 = lean_ctor_get(x_134, 3);
lean_inc(x_140);
x_141 = lean_ctor_get(x_134, 4);
lean_inc(x_141);
x_142 = lean_ctor_get(x_134, 5);
lean_inc(x_142);
x_143 = lean_ctor_get(x_134, 6);
lean_inc(x_143);
x_144 = lean_ctor_get(x_134, 7);
lean_inc(x_144);
x_145 = lean_box(0);
x_146 = lean_box(0);
lean_inc(x_131);
lean_inc(x_19);
x_147 = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_19);
lean_ctor_set(x_147, 2, x_112);
lean_ctor_set(x_147, 3, x_128);
lean_ctor_set(x_147, 4, x_131);
x_148 = lean_unbox(x_136);
lean_ctor_set_uint8(x_147, sizeof(void*)*5, x_148);
x_149 = lean_unbox(x_146);
lean_ctor_set_uint8(x_147, sizeof(void*)*5 + 1, x_149);
x_150 = lean_array_push(x_144, x_147);
x_151 = lean_ctor_get(x_134, 8);
lean_inc(x_151);
x_152 = lean_ctor_get(x_134, 9);
lean_inc(x_152);
x_153 = lean_ctor_get(x_134, 10);
lean_inc(x_153);
x_154 = lean_ctor_get(x_134, 11);
lean_inc(x_154);
lean_dec(x_134);
x_155 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_155, 0, x_137);
lean_ctor_set(x_155, 1, x_138);
lean_ctor_set(x_155, 2, x_139);
lean_ctor_set(x_155, 3, x_140);
lean_ctor_set(x_155, 4, x_141);
lean_ctor_set(x_155, 5, x_142);
lean_ctor_set(x_155, 6, x_143);
lean_ctor_set(x_155, 7, x_150);
lean_ctor_set(x_155, 8, x_151);
lean_ctor_set(x_155, 9, x_152);
lean_ctor_set(x_155, 10, x_153);
lean_ctor_set(x_155, 11, x_154);
x_156 = lean_st_ref_set(x_2, x_155, x_135);
x_157 = lean_ctor_get(x_156, 1);
lean_inc(x_157);
lean_dec(x_156);
x_158 = lean_st_ref_take(x_2, x_157);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = lean_ctor_get(x_159, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_159, 1);
lean_inc(x_162);
x_163 = lean_ctor_get(x_159, 2);
lean_inc(x_163);
x_164 = lean_ctor_get(x_159, 3);
lean_inc(x_164);
x_165 = lean_ctor_get(x_159, 4);
lean_inc(x_165);
x_166 = lean_ctor_get(x_159, 5);
lean_inc(x_166);
x_167 = lean_array_size(x_166);
x_168 = lean_unsigned_to_nat(0u);
x_169 = lean_usize_of_nat(x_168);
x_170 = l_Array_mapMUnsafe_map___at___Lean_Meta_Closure_process_spec__1(x_19, x_131, x_167, x_169, x_166);
lean_dec(x_131);
x_171 = lean_ctor_get(x_159, 6);
lean_inc(x_171);
x_172 = lean_ctor_get(x_159, 7);
lean_inc(x_172);
x_173 = lean_ctor_get(x_159, 8);
lean_inc(x_173);
x_174 = lean_ctor_get(x_159, 9);
lean_inc(x_174);
x_175 = lean_ctor_get(x_159, 10);
lean_inc(x_175);
x_176 = lean_ctor_get(x_159, 11);
lean_inc(x_176);
lean_dec(x_159);
x_177 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_177, 0, x_161);
lean_ctor_set(x_177, 1, x_162);
lean_ctor_set(x_177, 2, x_163);
lean_ctor_set(x_177, 3, x_164);
lean_ctor_set(x_177, 4, x_165);
lean_ctor_set(x_177, 5, x_170);
lean_ctor_set(x_177, 6, x_171);
lean_ctor_set(x_177, 7, x_172);
lean_ctor_set(x_177, 8, x_173);
lean_ctor_set(x_177, 9, x_174);
lean_ctor_set(x_177, 10, x_175);
lean_ctor_set(x_177, 11, x_176);
x_178 = lean_st_ref_set(x_2, x_177, x_160);
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
lean_dec(x_178);
x_7 = x_179;
goto _start;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_128);
lean_dec(x_112);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_181 = lean_ctor_get(x_130, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_130, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_183 = x_130;
} else {
 lean_dec_ref(x_130);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(1, 2, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_182);
return x_184;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_114);
lean_dec(x_112);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_185 = lean_ctor_get(x_127, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_127, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_187 = x_127;
} else {
 lean_dec_ref(x_127);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_186);
return x_188;
}
}
}
}
}
else
{
uint8_t x_189; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_189 = !lean_is_exclusive(x_20);
if (x_189 == 0)
{
return x_20;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_20, 0);
x_191 = lean_ctor_get(x_20, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_20);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___Lean_Meta_Closure_process_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_findCore___at___Lean_Meta_Closure_process_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___Lean_Meta_Closure_process_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_findCore___at___Lean_Meta_Closure_process_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Closure_process_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___at___Lean_Meta_Closure_process_spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_Meta_Closure_process(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_array_fget(x_1, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 3);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_8, sizeof(void*)*4);
lean_dec(x_8);
x_12 = lean_expr_abstract_range(x_10, x_5, x_2);
lean_dec(x_10);
if (x_3 == 0)
{
lean_object* x_13; 
x_13 = l_Lean_Expr_forallE___override(x_9, x_12, x_7, x_11);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = l_Lean_Expr_lam___override(x_9, x_12, x_7, x_11);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_8, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_8, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_8, 4);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_8, sizeof(void*)*5);
lean_dec(x_8);
x_19 = lean_expr_has_loose_bvar(x_7, x_4);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_expr_lower_loose_bvars(x_7, x_20, x_20);
lean_dec(x_7);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_expr_abstract_range(x_16, x_5, x_2);
lean_dec(x_16);
x_23 = lean_expr_abstract_range(x_17, x_5, x_2);
lean_dec(x_17);
x_24 = l_Lean_Expr_letE___override(x_15, x_22, x_23, x_7, x_18);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; lean_object* x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_4 = lean_alloc_closure((void*)(l_Lean_LocalDecl_toExpr), 1, 0);
x_5 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_6 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_7 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_8 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_9 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_10 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_11 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_6);
x_13 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
lean_ctor_set(x_13, 2, x_8);
lean_ctor_set(x_13, 3, x_9);
lean_ctor_set(x_13, 4, x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
x_15 = lean_array_size(x_2);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_usize_of_nat(x_16);
lean_inc(x_2);
x_18 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_14, x_4, x_15, x_17, x_2);
x_19 = lean_box(x_1);
lean_inc(x_18);
lean_inc(x_2);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_Closure_mkBinding___lam__0___boxed), 7, 4);
lean_closure_set(x_20, 0, x_2);
lean_closure_set(x_20, 1, x_18);
lean_closure_set(x_20, 2, x_19);
lean_closure_set(x_20, 3, x_16);
x_21 = lean_expr_abstract(x_3, x_18);
lean_dec(x_18);
x_22 = lean_array_get_size(x_2);
lean_dec(x_2);
x_23 = l_Nat_foldRev___redArg(x_22, x_20, x_21);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = l_Lean_Meta_Closure_mkBinding___lam__0(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Meta_Closure_mkBinding(x_4, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Closure_mkLambda_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = l_Lean_LocalDecl_toExpr(x_5);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_array_fget(x_1, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 3);
lean_inc(x_9);
x_10 = lean_ctor_get_uint8(x_7, sizeof(void*)*4);
lean_dec(x_7);
x_11 = lean_expr_abstract_range(x_9, x_4, x_2);
lean_dec(x_9);
x_12 = l_Lean_Expr_lam___override(x_8, x_11, x_6, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_7, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 4);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_7, sizeof(void*)*5);
lean_dec(x_7);
x_17 = lean_expr_has_loose_bvar(x_6, x_3);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_expr_lower_loose_bvars(x_6, x_18, x_18);
lean_dec(x_6);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_expr_abstract_range(x_14, x_4, x_2);
lean_dec(x_14);
x_21 = lean_expr_abstract_range(x_15, x_4, x_2);
lean_dec(x_15);
x_22 = l_Lean_Expr_letE___override(x_13, x_20, x_21, x_6, x_16);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_usize_of_nat(x_4);
lean_inc(x_1);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Meta_Closure_mkLambda_spec__0(x_3, x_5, x_1);
lean_inc(x_6);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_Closure_mkLambda___lam__0___boxed), 6, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_6);
lean_closure_set(x_7, 2, x_4);
x_8 = lean_expr_abstract(x_2, x_6);
lean_dec(x_6);
x_9 = lean_array_get_size(x_1);
lean_dec(x_1);
x_10 = l_Nat_foldRev___redArg(x_9, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Closure_mkLambda_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Meta_Closure_mkLambda_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Closure_mkLambda___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Closure_mkLambda(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_array_fget(x_1, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 3);
lean_inc(x_9);
x_10 = lean_ctor_get_uint8(x_7, sizeof(void*)*4);
lean_dec(x_7);
x_11 = lean_expr_abstract_range(x_9, x_4, x_2);
lean_dec(x_9);
x_12 = l_Lean_Expr_forallE___override(x_8, x_11, x_6, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_7, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 4);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_7, sizeof(void*)*5);
lean_dec(x_7);
x_17 = lean_expr_has_loose_bvar(x_6, x_3);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_expr_lower_loose_bvars(x_6, x_18, x_18);
lean_dec(x_6);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_expr_abstract_range(x_14, x_4, x_2);
lean_dec(x_14);
x_21 = lean_expr_abstract_range(x_15, x_4, x_2);
lean_dec(x_15);
x_22 = l_Lean_Expr_letE___override(x_13, x_20, x_21, x_6, x_16);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_usize_of_nat(x_4);
lean_inc(x_1);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Meta_Closure_mkLambda_spec__0(x_3, x_5, x_1);
lean_inc(x_6);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_Closure_mkForall___lam__0___boxed), 6, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_6);
lean_closure_set(x_7, 2, x_4);
x_8 = lean_expr_abstract(x_2, x_6);
lean_dec(x_6);
x_9 = lean_array_get_size(x_1);
lean_dec(x_1);
x_10 = l_Nat_foldRev___redArg(x_9, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Closure_mkForall___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Closure_mkForall(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_st_ref_take(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 4);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_2);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_41; uint64_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_10 = l_Lean_Meta_resetZetaDeltaFVarIds___redArg(x_6, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_get(x_6, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_take(x_6, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_19);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_inc(x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_19);
lean_inc(x_19);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_19);
lean_inc(x_23);
lean_inc(x_20);
x_24 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 3, x_20);
lean_ctor_set(x_24, 4, x_23);
lean_ctor_set(x_24, 5, x_23);
x_25 = lean_ctor_get(x_16, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_16, 3);
lean_inc(x_26);
x_27 = lean_ctor_get(x_16, 4);
lean_inc(x_27);
lean_dec(x_16);
x_28 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set(x_28, 3, x_26);
lean_ctor_set(x_28, 4, x_27);
x_29 = lean_st_ref_set(x_6, x_28, x_17);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_dec(x_13);
x_41 = lean_ctor_get(x_5, 0);
x_42 = lean_ctor_get_uint64(x_5, sizeof(void*)*7);
x_43 = lean_box(1);
x_44 = lean_ctor_get(x_5, 1);
x_45 = lean_ctor_get(x_5, 2);
x_46 = lean_ctor_get(x_5, 3);
x_47 = lean_ctor_get(x_5, 4);
x_48 = lean_ctor_get(x_5, 5);
x_49 = lean_ctor_get(x_5, 6);
x_50 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 9);
x_51 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 10);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_41);
x_52 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_52, 0, x_41);
lean_ctor_set(x_52, 1, x_44);
lean_ctor_set(x_52, 2, x_45);
lean_ctor_set(x_52, 3, x_46);
lean_ctor_set(x_52, 4, x_47);
lean_ctor_set(x_52, 5, x_48);
lean_ctor_set(x_52, 6, x_49);
lean_ctor_set_uint64(x_52, sizeof(void*)*7, x_42);
x_53 = lean_unbox(x_43);
lean_ctor_set_uint8(x_52, sizeof(void*)*7 + 8, x_53);
lean_ctor_set_uint8(x_52, sizeof(void*)*7 + 9, x_50);
lean_ctor_set_uint8(x_52, sizeof(void*)*7 + 10, x_51);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_52);
lean_inc(x_4);
x_54 = l_Lean_Meta_Closure_collectExpr(x_1, x_3, x_4, x_52, x_6, x_7, x_8, x_30);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_52);
lean_inc(x_4);
x_57 = l_Lean_Meta_Closure_collectExpr(x_2, x_3, x_4, x_52, x_6, x_7, x_8, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_inc(x_6);
x_60 = l_Lean_Meta_Closure_process(x_3, x_4, x_52, x_6, x_7, x_8, x_59);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_62 = lean_ctor_get(x_60, 1);
x_63 = lean_ctor_get(x_60, 0);
lean_dec(x_63);
lean_ctor_set(x_60, 1, x_58);
lean_ctor_set(x_60, 0, x_55);
lean_inc(x_60);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_60);
x_65 = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(x_6, x_31, x_64, x_62);
lean_dec(x_64);
lean_dec(x_6);
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_65, 0);
lean_dec(x_67);
lean_ctor_set(x_65, 0, x_60);
return x_65;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec(x_65);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_60);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_70 = lean_ctor_get(x_60, 1);
lean_inc(x_70);
lean_dec(x_60);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_55);
lean_ctor_set(x_71, 1, x_58);
lean_inc(x_71);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(x_6, x_31, x_72, x_70);
lean_dec(x_72);
lean_dec(x_6);
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
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_71);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_58);
lean_dec(x_55);
x_77 = lean_ctor_get(x_60, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_60, 1);
lean_inc(x_78);
lean_dec(x_60);
x_32 = x_77;
x_33 = x_78;
goto block_40;
}
}
else
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_79 = lean_ctor_get(x_57, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_57, 1);
lean_inc(x_80);
lean_dec(x_57);
x_32 = x_79;
x_33 = x_80;
goto block_40;
}
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_52);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_81 = lean_ctor_get(x_54, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_54, 1);
lean_inc(x_82);
lean_dec(x_54);
x_32 = x_81;
x_33 = x_82;
goto block_40;
}
block_40:
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_box(0);
x_35 = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(x_6, x_31, x_34, x_33);
lean_dec(x_6);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 0, x_32);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Meta_Closure_mkValueTypeClosureAux(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
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
x_23 = lean_unsigned_to_nat(1u);
lean_inc_n(x_22, 7);
x_24 = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set(x_24, 4, x_22);
lean_ctor_set(x_24, 5, x_22);
lean_ctor_set(x_24, 6, x_22);
lean_ctor_set(x_24, 7, x_22);
lean_ctor_set(x_24, 8, x_23);
lean_ctor_set(x_24, 9, x_22);
lean_ctor_set(x_24, 10, x_22);
lean_ctor_set(x_24, 11, x_22);
x_25 = lean_st_mk_ref(x_24, x_8);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_26);
x_28 = l_Lean_Meta_Closure_mkValueTypeClosureAux(x_1, x_2, x_3, x_26, x_4, x_5, x_6, x_7, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_st_ref_get(x_26, x_30);
lean_dec(x_26);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_ctor_get(x_33, 5);
lean_inc(x_36);
x_37 = l_Array_reverse(lean_box(0), x_36);
x_38 = lean_ctor_get(x_33, 6);
lean_inc(x_38);
x_39 = l_Array_append(lean_box(0), x_37, x_38);
lean_dec(x_38);
x_40 = lean_ctor_get(x_33, 7);
lean_inc(x_40);
x_41 = l_Array_reverse(lean_box(0), x_40);
lean_inc(x_41);
x_42 = l_Lean_Meta_Closure_mkForall(x_41, x_34);
lean_dec(x_34);
lean_inc(x_39);
x_43 = l_Lean_Meta_Closure_mkForall(x_39, x_42);
lean_dec(x_42);
x_44 = l_Lean_Meta_Closure_mkLambda(x_41, x_35);
lean_dec(x_35);
x_45 = l_Lean_Meta_Closure_mkLambda(x_39, x_44);
lean_dec(x_44);
x_46 = lean_ctor_get(x_33, 2);
lean_inc(x_46);
x_47 = lean_ctor_get(x_33, 4);
lean_inc(x_47);
x_48 = lean_ctor_get(x_33, 10);
lean_inc(x_48);
x_49 = l_Array_reverse(lean_box(0), x_48);
x_50 = lean_ctor_get(x_33, 9);
lean_inc(x_50);
lean_dec(x_33);
x_51 = l_Array_append(lean_box(0), x_49, x_50);
lean_dec(x_50);
x_52 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_52, 0, x_46);
lean_ctor_set(x_52, 1, x_43);
lean_ctor_set(x_52, 2, x_45);
lean_ctor_set(x_52, 3, x_47);
lean_ctor_set(x_52, 4, x_51);
lean_ctor_set(x_31, 0, x_52);
return x_31;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_53 = lean_ctor_get(x_31, 0);
x_54 = lean_ctor_get(x_31, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_31);
x_55 = lean_ctor_get(x_29, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_29, 1);
lean_inc(x_56);
lean_dec(x_29);
x_57 = lean_ctor_get(x_53, 5);
lean_inc(x_57);
x_58 = l_Array_reverse(lean_box(0), x_57);
x_59 = lean_ctor_get(x_53, 6);
lean_inc(x_59);
x_60 = l_Array_append(lean_box(0), x_58, x_59);
lean_dec(x_59);
x_61 = lean_ctor_get(x_53, 7);
lean_inc(x_61);
x_62 = l_Array_reverse(lean_box(0), x_61);
lean_inc(x_62);
x_63 = l_Lean_Meta_Closure_mkForall(x_62, x_55);
lean_dec(x_55);
lean_inc(x_60);
x_64 = l_Lean_Meta_Closure_mkForall(x_60, x_63);
lean_dec(x_63);
x_65 = l_Lean_Meta_Closure_mkLambda(x_62, x_56);
lean_dec(x_56);
x_66 = l_Lean_Meta_Closure_mkLambda(x_60, x_65);
lean_dec(x_65);
x_67 = lean_ctor_get(x_53, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_53, 4);
lean_inc(x_68);
x_69 = lean_ctor_get(x_53, 10);
lean_inc(x_69);
x_70 = l_Array_reverse(lean_box(0), x_69);
x_71 = lean_ctor_get(x_53, 9);
lean_inc(x_71);
lean_dec(x_53);
x_72 = l_Array_append(lean_box(0), x_70, x_71);
lean_dec(x_71);
x_73 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_73, 0, x_67);
lean_ctor_set(x_73, 1, x_64);
lean_ctor_set(x_73, 2, x_66);
lean_ctor_set(x_73, 3, x_68);
lean_ctor_set(x_73, 4, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_54);
return x_74;
}
}
else
{
uint8_t x_75; 
lean_dec(x_26);
x_75 = !lean_is_exclusive(x_28);
if (x_75 == 0)
{
return x_28;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_28, 0);
x_77 = lean_ctor_get(x_28, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_28);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_Closure_mkValueTypeClosure(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferrringUnsafe___at___Lean_Meta_mkAuxDefinition_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_19; lean_object* x_25; uint8_t x_26; 
x_8 = lean_st_ref_get(x_6, x_7);
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
x_25 = lean_ctor_get(x_9, 0);
lean_inc(x_25);
lean_dec(x_9);
lean_inc(x_25);
x_26 = l_Lean_Environment_hasUnsafe(x_25, x_3);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = l_Lean_Environment_hasUnsafe(x_25, x_4);
x_19 = x_27;
goto block_24;
}
else
{
lean_dec(x_25);
x_19 = x_26;
goto block_24;
}
block_18:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_inc(x_1);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set(x_13, 2, x_3);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_4);
lean_ctor_set(x_16, 2, x_5);
lean_ctor_set(x_16, 3, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*4, x_12);
if (lean_is_scalar(x_11)) {
 x_17 = lean_alloc_ctor(0, 2, 0);
} else {
 x_17 = x_11;
}
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
block_24:
{
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_box(1);
x_21 = lean_unbox(x_20);
x_12 = x_21;
goto block_18;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_box(0);
x_23 = lean_unbox(x_22);
x_12 = x_23;
goto block_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferrringUnsafe___at___Lean_Meta_mkAuxDefinition_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_mkDefinitionValInferrringUnsafe___at___Lean_Meta_mkAuxDefinition_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
x_11 = l_Lean_Meta_Closure_mkValueTypeClosure(x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint32_t x_28; lean_object* x_29; uint32_t x_30; uint32_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
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
x_23 = lean_st_ref_get(x_9, x_13);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_12, 2);
lean_inc(x_27);
lean_inc(x_27);
x_28 = l_Lean_getMaxHeight(x_26, x_27);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_uint32_of_nat(x_29);
x_31 = lean_uint32_add(x_28, x_30);
x_32 = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(x_32, 0, x_31);
x_33 = lean_ctor_get(x_12, 0);
lean_inc(x_33);
x_34 = lean_array_to_list(x_33);
x_35 = lean_ctor_get(x_12, 1);
lean_inc(x_35);
lean_inc(x_1);
x_36 = l_Lean_mkDefinitionValInferrringUnsafe___at___Lean_Meta_mkAuxDefinition_spec__0___redArg(x_1, x_34, x_35, x_27, x_32, x_9, x_25);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_37);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_39);
x_40 = l_Lean_addDecl(x_39, x_8, x_9, x_38);
if (lean_obj_tag(x_40) == 0)
{
if (x_5 == 0)
{
lean_object* x_41; 
lean_dec(x_39);
lean_dec(x_9);
lean_dec(x_8);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_15 = x_41;
goto block_22;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_compileDecl(x_39, x_5, x_8, x_9, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_15 = x_44;
goto block_22;
}
else
{
uint8_t x_45; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_43);
if (x_45 == 0)
{
return x_43;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_43, 0);
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_43);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_39);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
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
block_22:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_12, 3);
lean_inc(x_16);
x_17 = lean_array_to_list(x_16);
x_18 = l_Lean_Expr_const___override(x_1, x_17);
x_19 = lean_ctor_get(x_12, 4);
lean_inc(x_19);
lean_dec(x_12);
x_20 = l_Lean_mkAppN(x_18, x_19);
lean_dec(x_19);
if (lean_is_scalar(x_14)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_14;
}
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_15);
return x_21;
}
}
else
{
uint8_t x_53; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_11);
if (x_53 == 0)
{
return x_11;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_11, 0);
x_55 = lean_ctor_get(x_11, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_11);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferrringUnsafe___at___Lean_Meta_mkAuxDefinition_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_mkDefinitionValInferrringUnsafe___at___Lean_Meta_mkAuxDefinition_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferrringUnsafe___at___Lean_Meta_mkAuxDefinition_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_mkDefinitionValInferrringUnsafe___at___Lean_Meta_mkAuxDefinition_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_Meta_mkAuxDefinition(x_1, x_2, x_3, x_11, x_12, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_9 = lean_infer_type(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Expr_headBeta(x_10);
x_13 = lean_box(1);
x_14 = lean_unbox(x_13);
x_15 = l_Lean_Meta_mkAuxDefinition(x_1, x_12, x_2, x_3, x_14, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_4);
return x_15;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_mkAuxDefinitionFor(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxTheorem(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_11 = l_Lean_Meta_Closure_mkValueTypeClosure(x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_array_to_list(x_14);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_12, 2);
lean_inc(x_17);
x_18 = l_Lean_Meta_mkAuxLemma(x_15, x_16, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_7);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_12, 3);
lean_inc(x_21);
x_22 = lean_array_to_list(x_21);
x_23 = l_Lean_Expr_const___override(x_20, x_22);
x_24 = lean_ctor_get(x_12, 4);
lean_inc(x_24);
lean_dec(x_12);
x_25 = l_Lean_mkAppN(x_23, x_24);
lean_dec(x_24);
lean_ctor_set(x_18, 0, x_25);
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
x_28 = lean_ctor_get(x_12, 3);
lean_inc(x_28);
x_29 = lean_array_to_list(x_28);
x_30 = l_Lean_Expr_const___override(x_26, x_29);
x_31 = lean_ctor_get(x_12, 4);
lean_inc(x_31);
lean_dec(x_12);
x_32 = l_Lean_mkAppN(x_30, x_31);
lean_dec(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_27);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_12);
x_34 = !lean_is_exclusive(x_18);
if (x_34 == 0)
{
return x_18;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_18, 0);
x_36 = lean_ctor_get(x_18, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_18);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_38 = !lean_is_exclusive(x_11);
if (x_38 == 0)
{
return x_11;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_11, 0);
x_40 = lean_ctor_get(x_11, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_11);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxTheorem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_Meta_mkAuxTheorem(x_1, x_2, x_11, x_4, x_12, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_13;
}
}
lean_object* initialize_Lean_MetavarContext(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Environment(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_AddDecl(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_FoldConsts(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Check(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_AuxLemma(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Closure(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_MetavarContext(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_AddDecl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FoldConsts(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Check(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_AuxLemma(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Closure_instInhabitedToProcessElement = _init_l_Lean_Meta_Closure_instInhabitedToProcessElement();
lean_mark_persistent(l_Lean_Meta_Closure_instInhabitedToProcessElement);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
