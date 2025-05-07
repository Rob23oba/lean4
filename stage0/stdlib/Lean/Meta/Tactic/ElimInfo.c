// Lean compiler output
// Module: Lean.Meta.Tactic.ElimInfo
// Imports: Lean.Meta.Basic Lean.Meta.Check Lean.ScopedEnvExtension
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
LEAN_EXPORT lean_object* l_Lean_Meta_getElimInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addCustomEliminatorEntry(lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getElimExprInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_ElimInfo___hyg_3258_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__4___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_getElimExprInfo_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getElimExprInfo___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminator___redArg___lam__0____x40_Lean_Meta_Tactic_ElimInfo___hyg_2292_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addCustomEliminator_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Tactic_ElimInfo___hyg_3258_(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__3___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__4_spec__4_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___Lean_Meta_addImplicitTargets_collect_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_40_(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedCustomEliminators;
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_addImplicitTargets_spec__6___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminator____x40_Lean_Meta_Tactic_ElimInfo___hyg_2292____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_SMap_fold___at___Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_getElimExprInfo_spec__5_spec__5___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminators;
LEAN_EXPORT uint64_t l_Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__0(lean_object*, size_t, size_t, uint64_t);
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addCustomEliminator___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__4_spec__4_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Tactic_ElimInfo___hyg_3258____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_getElimExprInfo_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3026_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___Array_finIdxOf_x3f___at___Array_idxOf_x3f___at___Lean_Meta_getElimExprInfo_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_instHashableBool___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__4_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminator_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_contains___at___Lean_Meta_addImplicitTargets_collect_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_addImplicitTargets_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___Lean_Meta_initFn____x40_Lean_Meta_Tactic_ElimInfo___hyg_2474__spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_addImplicitTargets_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Format_joinSep(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_addImplicitTargets_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___Lean_Meta_mkCustomEliminator_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_addImplicitTargets_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqProd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminator___redArg____x40_Lean_Meta_Tactic_ElimInfo___hyg_2292_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCustomEliminator___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_altArity(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instBEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators___redArg___lam__0____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408_(uint8_t, uint8_t);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_SMap_fold___at___Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addCustomEliminator_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addCustomEliminator(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isSort(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__4_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminator____x40_Lean_Meta_Tactic_ElimInfo___hyg_2292_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_getElimExprInfo_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo___redArg____x40_Lean_Meta_Tactic_ElimInfo___hyg_40_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_ElimInfo___hyg_2474_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___Lean_Meta_initFn____x40_Lean_Meta_Tactic_ElimInfo___hyg_2474__spec__0(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_to_int(lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__1____x40_Lean_Meta_Tactic_ElimInfo___hyg_3180_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_getElimExprInfo_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_SMap_fold___at___Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__4_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminators(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminator_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_40____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getCustomEliminator_x3f_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_getElimExprInfo_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__1____x40_Lean_Meta_Tactic_ElimInfo___hyg_3180____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__3_spec__3_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo___redArg____x40_Lean_Meta_Tactic_ElimInfo___hyg_217_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminators___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Tactic_ElimInfo___hyg_3180____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at___Lean_Meta_arrowDomainsN_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addImplicitTargets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Array_contains___at___Lean_Meta_addImplicitTargets_collect_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT uint8_t l_Array_contains___at___Lean_Meta_addImplicitTargets_collect_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getCustomEliminator_x3f_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_Meta_addImplicitTargets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCustomEliminator(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__3_spec__3_spec__3_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getCustomEliminator_x3f_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprElimAltInfo;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_addImplicitTargets_spec__6(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprElimInfo;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_getElimExprInfo_spec__5_spec__5___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_getElimExprInfo_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedElimInfo;
uint64_t l___private_Lean_Expr_0__Lean_hashMVarId____x40_Lean_Expr___hyg_1984_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedCustomEliminator;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedElimAltInfo;
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_217____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo___redArg___lam__0____x40_Lean_Meta_Tactic_ElimInfo___hyg_217_(lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___Array_idxOf_x3f___at___Lean_Meta_getElimExprInfo_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_customEliminatorExt;
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__3_spec__3_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___Lean_Meta_getElimExprInfo_spec__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addImplicitTargets_collect___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators___redArg___lam__0____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408____boxed(lean_object*, lean_object*);
lean_object* l_Array_takeWhile___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__3_spec__3_spec__3_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___Array_finIdxOf_x3f___at___Array_idxOf_x3f___at___Lean_Meta_getElimExprInfo_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_instHashableArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators___redArg____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___Lean_Meta_mkCustomEliminator_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___Lean_Meta_mkCustomEliminator_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getCustomEliminator_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo___redArg___lam__1____x40_Lean_Meta_Tactic_ElimInfo___hyg_217_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCustomEliminator___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_addImplicitTargets_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHasTypeButIsExpectedMsg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators___redArg____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408_(lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_addImplicitTargets_spec__4_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addCustomEliminator_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___Array_idxOf_x3f___at___Lean_Meta_getElimExprInfo_spec__0_spec__0(lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Tactic_ElimInfo___hyg_3180_(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_SMap_fold___at___Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_altArity___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Option_repr___at___Lean_Environment_dbgFormatAsyncState_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___Lean_Meta_initFn____x40_Lean_Meta_Tactic_ElimInfo___hyg_2474__spec__0___redArg___boxed(lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_getElimExprInfo_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_size___redArg(lean_object*);
lean_object* l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_instInhabitedEntry(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__4_spec__4_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___Lean_Meta_getElimExprInfo_spec__0(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminators___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminators___redArg___boxed(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__0(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCustomEliminator;
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_instHashableProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCustomEliminator___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_217_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_SMap_fold___at___Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*, size_t, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getElimExprInfo___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_instBEq;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_getElimExprInfo_spec__5_spec__5___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Tactic_ElimInfo___hyg_2474____boxed(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_ElimInfo___hyg_3180_(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_SMap_fold___at___Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addCustomEliminator_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__0___boxed(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408_(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___Lean_Meta_initFn____x40_Lean_Meta_Tactic_ElimInfo___hyg_2474__spec__0___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addImplicitTargets_collect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_getElimExprInfo_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_getElimExprInfo_spec__5_spec__5___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Tactic_ElimInfo___hyg_2474_(lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_getElimExprInfo_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_getElimExprInfo_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instHashableName;
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___Lean_Meta_mkCustomEliminator_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo___redArg____x40_Lean_Meta_Tactic_ElimInfo___hyg_40_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_74; 
x_2 = lean_mk_string_unchecked("{ ", 2, 2);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("name", 4, 4);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_mk_string_unchecked(" := ", 4, 4);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_inc(x_8);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(8u);
x_11 = lean_nat_to_int(x_10);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Name_reprPrec(x_12, x_13);
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_17, 0, x_15);
x_18 = lean_unbox(x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_18);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_mk_string_unchecked(",", 1, 1);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_inc(x_21);
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_box(1);
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_mk_string_unchecked("declName\?", 9, 9);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
lean_inc(x_8);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
x_29 = lean_unsigned_to_nat(13u);
x_30 = lean_nat_to_int(x_29);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
x_32 = l_Option_repr___at___Lean_Environment_dbgFormatAsyncState_spec__6(x_31, x_13);
lean_inc(x_30);
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_unbox(x_16);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_35);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_34);
lean_inc(x_21);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_21);
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_23);
x_39 = lean_mk_string_unchecked("numFields", 9, 9);
x_40 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
lean_inc(x_8);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_8);
x_43 = lean_ctor_get(x_1, 2);
lean_inc(x_43);
x_44 = l___private_Init_Data_Repr_0__Nat_reprFast(x_43);
x_45 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_46, 0, x_30);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_unbox(x_16);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_48);
x_49 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_49, 0, x_42);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_21);
x_51 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_23);
x_52 = lean_mk_string_unchecked("provesMotive", 12, 12);
x_53 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_8);
x_56 = lean_unsigned_to_nat(16u);
x_57 = lean_nat_to_int(x_56);
x_74 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_dec(x_1);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_mk_string_unchecked("false", 5, 5);
x_76 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_58 = x_76;
goto block_73;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_mk_string_unchecked("true", 4, 4);
x_78 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_58 = x_78;
goto block_73;
}
block_73:
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_59 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_unbox(x_16);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_61);
x_62 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_62, 0, x_55);
lean_ctor_set(x_62, 1, x_60);
x_63 = lean_mk_string_unchecked(" }", 2, 2);
x_64 = lean_unsigned_to_nat(2u);
x_65 = lean_nat_to_int(x_64);
x_66 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_66, 0, x_2);
x_67 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_62);
x_68 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_68, 0, x_63);
x_69 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_70, 0, x_65);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_71, 0, x_70);
x_72 = lean_unbox(x_16);
lean_ctor_set_uint8(x_71, sizeof(void*)*1, x_72);
return x_71;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_40_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo___redArg____x40_Lean_Meta_Tactic_ElimInfo___hyg_40_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_40____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_40_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instReprElimAltInfo() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_40____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedElimAltInfo() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
x_6 = lean_unbox(x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_6);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo___redArg___lam__0____x40_Lean_Meta_Tactic_ElimInfo___hyg_217_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo___redArg____x40_Lean_Meta_Tactic_ElimInfo___hyg_40_(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo___redArg___lam__1____x40_Lean_Meta_Tactic_ElimInfo___hyg_217_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo___redArg____x40_Lean_Meta_Tactic_ElimInfo___hyg_217_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo___redArg___lam__0____x40_Lean_Meta_Tactic_ElimInfo___hyg_217_), 1, 0);
x_3 = lean_mk_string_unchecked("{ ", 2, 2);
x_4 = lean_box(0);
x_5 = lean_mk_string_unchecked("elimExpr", 8, 8);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_mk_string_unchecked(" := ", 4, 4);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_inc(x_9);
x_10 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_unsigned_to_nat(12u);
x_12 = lean_nat_to_int(x_11);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3026_(x_13, x_14);
lean_inc(x_12);
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_18, 0, x_16);
x_19 = lean_unbox(x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_19);
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_mk_string_unchecked(",", 1, 1);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_inc(x_22);
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_box(1);
x_57 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_57, 0, x_23);
lean_ctor_set(x_57, 1, x_24);
x_58 = lean_mk_string_unchecked("elimType", 8, 8);
x_59 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_59);
lean_inc(x_9);
x_61 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_9);
x_62 = lean_ctor_get(x_1, 1);
lean_inc(x_62);
x_63 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3026_(x_62, x_14);
lean_inc(x_12);
x_64 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_64, 0, x_12);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_unbox(x_17);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_66);
x_67 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_67, 0, x_61);
lean_ctor_set(x_67, 1, x_65);
lean_inc(x_22);
x_68 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_22);
x_69 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_24);
x_70 = lean_mk_string_unchecked("motivePos", 9, 9);
x_71 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_71);
lean_inc(x_9);
x_73 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_9);
x_74 = lean_unsigned_to_nat(13u);
x_75 = lean_nat_to_int(x_74);
x_76 = lean_ctor_get(x_1, 2);
lean_inc(x_76);
x_77 = l___private_Init_Data_Repr_0__Nat_reprFast(x_76);
x_78 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_79 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_80, 0, x_79);
x_81 = lean_unbox(x_17);
lean_ctor_set_uint8(x_80, sizeof(void*)*1, x_81);
x_82 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_82, 0, x_73);
lean_ctor_set(x_82, 1, x_80);
lean_inc(x_22);
x_83 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_22);
x_84 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_24);
x_85 = lean_mk_string_unchecked("targetsPos", 10, 10);
x_86 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_87 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_86);
lean_inc(x_9);
x_88 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_9);
x_89 = lean_unsigned_to_nat(14u);
x_90 = lean_nat_to_int(x_89);
x_121 = lean_ctor_get(x_1, 3);
lean_inc(x_121);
x_122 = lean_array_get_size(x_121);
x_123 = lean_nat_dec_eq(x_122, x_14);
lean_dec(x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_124 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo___redArg___lam__1____x40_Lean_Meta_Tactic_ElimInfo___hyg_217_), 1, 0);
x_125 = lean_mk_string_unchecked("#[", 2, 2);
x_126 = lean_array_to_list(x_121);
lean_inc(x_22);
x_127 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_127, 0, x_22);
lean_ctor_set(x_127, 1, x_24);
x_128 = l_Std_Format_joinSep(lean_box(0), x_124, x_126, x_127);
x_129 = lean_mk_string_unchecked("]", 1, 1);
x_130 = lean_unsigned_to_nat(2u);
x_131 = lean_nat_to_int(x_130);
x_132 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_132, 0, x_125);
x_133 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_128);
x_134 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_134, 0, x_129);
x_135 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_136, 0, x_131);
lean_ctor_set(x_136, 1, x_135);
x_137 = l_Std_Format_fill(x_136);
x_91 = x_137;
goto block_120;
}
else
{
lean_object* x_138; lean_object* x_139; 
lean_dec(x_121);
x_138 = lean_mk_string_unchecked("#[]", 3, 3);
x_139 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_139, 0, x_138);
x_91 = x_139;
goto block_120;
}
block_56:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_27 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_unbox(x_17);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_29);
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_22);
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_24);
x_33 = lean_mk_string_unchecked("numComplexMotiveArgs", 20, 20);
x_34 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_9);
x_37 = lean_unsigned_to_nat(24u);
x_38 = lean_nat_to_int(x_37);
x_39 = lean_ctor_get(x_1, 5);
lean_inc(x_39);
lean_dec(x_1);
x_40 = l___private_Init_Data_Repr_0__Nat_reprFast(x_39);
x_41 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_unbox(x_17);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_44);
x_45 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_45, 0, x_36);
lean_ctor_set(x_45, 1, x_43);
x_46 = lean_mk_string_unchecked(" }", 2, 2);
x_47 = lean_unsigned_to_nat(2u);
x_48 = lean_nat_to_int(x_47);
x_49 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_49, 0, x_3);
x_50 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_45);
x_51 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_51, 0, x_46);
x_52 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_unbox(x_17);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_55);
return x_54;
}
block_120:
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_92 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_93, 0, x_92);
x_94 = lean_unbox(x_17);
lean_ctor_set_uint8(x_93, sizeof(void*)*1, x_94);
x_95 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_95, 0, x_88);
lean_ctor_set(x_95, 1, x_93);
lean_inc(x_22);
x_96 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_22);
x_97 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_24);
x_98 = lean_mk_string_unchecked("altsInfo", 8, 8);
x_99 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_99, 0, x_98);
x_100 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_99);
lean_inc(x_9);
x_101 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_9);
x_102 = lean_ctor_get(x_1, 4);
lean_inc(x_102);
x_103 = lean_array_get_size(x_102);
x_104 = lean_nat_dec_eq(x_103, x_14);
lean_dec(x_103);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_105 = lean_mk_string_unchecked("#[", 2, 2);
x_106 = lean_array_to_list(x_102);
lean_inc(x_22);
x_107 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_107, 0, x_22);
lean_ctor_set(x_107, 1, x_24);
x_108 = l_Std_Format_joinSep(lean_box(0), x_2, x_106, x_107);
x_109 = lean_mk_string_unchecked("]", 1, 1);
x_110 = lean_unsigned_to_nat(2u);
x_111 = lean_nat_to_int(x_110);
x_112 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_112, 0, x_105);
x_113 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_108);
x_114 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_114, 0, x_109);
x_115 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_116, 0, x_111);
lean_ctor_set(x_116, 1, x_115);
x_117 = l_Std_Format_fill(x_116);
x_25 = x_101;
x_26 = x_117;
goto block_56;
}
else
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_102);
lean_dec(x_2);
x_118 = lean_mk_string_unchecked("#[]", 3, 3);
x_119 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_119, 0, x_118);
x_25 = x_101;
x_26 = x_119;
goto block_56;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_217_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo___redArg____x40_Lean_Meta_Tactic_ElimInfo___hyg_217_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_217____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_217_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instReprElimInfo() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_217____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedElimInfo() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(0);
x_4 = l_Lean_Expr_const___override(x_2, x_3);
x_5 = lean_box(0);
x_6 = l_Array_empty(lean_box(0));
lean_inc(x_6);
lean_inc(x_4);
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_5);
lean_ctor_set(x_7, 3, x_6);
lean_ctor_set(x_7, 4, x_6);
lean_ctor_set(x_7, 5, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_altArity(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 7:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 2);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_2, x_5);
lean_dec(x_2);
x_2 = x_6;
x_3 = x_4;
goto _start;
}
case 8:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 3);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_2, x_9);
lean_dec(x_2);
x_2 = x_10;
x_3 = x_8;
goto _start;
}
default: 
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l_Lean_Expr_getAppFn(x_3);
x_13 = lean_expr_eqv(x_12, x_1);
lean_dec(x_12);
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_altArity___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_altArity(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___Array_finIdxOf_x3f___at___Array_idxOf_x3f___at___Lean_Meta_getElimExprInfo_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_1, x_3);
x_8 = lean_expr_eqv(x_7, x_2);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_3);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___Array_idxOf_x3f___at___Lean_Meta_getElimExprInfo_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_idxOfAux___at___Array_finIdxOf_x3f___at___Array_idxOf_x3f___at___Lean_Meta_getElimExprInfo_spec__0_spec__0_spec__0(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___Lean_Meta_getElimExprInfo_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_finIdxOf_x3f___at___Array_idxOf_x3f___at___Lean_Meta_getElimExprInfo_spec__0_spec__0(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_getElimExprInfo_spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_24; 
x_13 = lean_array_uget(x_5, x_4);
x_14 = lean_box(0);
x_15 = lean_array_uset(x_5, x_4, x_14);
x_24 = l_Array_idxOf_x3f___at___Lean_Meta_getElimExprInfo_spec__0(x_1, x_13);
lean_dec(x_13);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_15);
x_25 = lean_mk_string_unchecked("unexpected eliminator type", 26, 26);
x_26 = l_Lean_stringToMessageData(x_25);
lean_dec(x_25);
x_27 = l_Lean_indentExpr(x_2);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_mk_string_unchecked("", 0, 0);
x_30 = l_Lean_stringToMessageData(x_29);
lean_dec(x_29);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_31, x_6, x_7, x_8, x_9, x_10);
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
lean_object* x_37; 
x_37 = lean_ctor_get(x_24, 0);
lean_inc(x_37);
lean_dec(x_24);
x_16 = x_37;
x_17 = x_10;
goto block_23;
}
block_23:
{
lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_add(x_4, x_19);
x_21 = lean_array_uset(x_15, x_4, x_16);
x_4 = x_20;
x_5 = x_21;
x_10 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_getElimExprInfo_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_nat_dec_lt(x_8, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_12);
return x_21;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_array_fget(x_1, x_8);
x_23 = lean_expr_eqv(x_22, x_2);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_Array_contains___at___Lean_Meta_arrowDomainsN_spec__0(x_3, x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_Expr_fvarId_x21(x_22);
lean_dec(x_22);
lean_inc(x_9);
x_26 = l_Lean_FVarId_getDecl___redArg(x_25, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_36; lean_object* x_37; lean_object* x_38; uint8_t x_45; uint8_t x_46; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_45 = l_Lean_LocalDecl_binderInfo(x_27);
x_46 = l_Lean_BinderInfo_isExplicit(x_45);
if (x_46 == 0)
{
lean_dec(x_27);
x_13 = x_7;
x_14 = x_28;
goto block_18;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_55; 
x_47 = lean_unsigned_to_nat(0u);
x_55 = lean_ctor_get(x_27, 3);
lean_inc(x_55);
x_48 = x_55;
goto block_54;
block_54:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = l_Lean_Meta_altArity(x_2, x_47, x_48);
lean_dec(x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_ctor_get(x_27, 2);
lean_inc(x_52);
lean_dec(x_27);
x_53 = lean_unbox(x_51);
lean_dec(x_51);
x_36 = x_53;
x_37 = x_50;
x_38 = x_52;
goto block_44;
}
}
block_35:
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*3, x_29);
x_34 = lean_array_push(x_7, x_33);
x_13 = x_34;
x_14 = x_28;
goto block_18;
}
block_44:
{
if (lean_obj_tag(x_4) == 0)
{
x_29 = x_36;
x_30 = x_38;
x_31 = x_37;
x_32 = x_4;
goto block_35;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_4, 0);
lean_inc(x_39);
lean_inc(x_38);
x_40 = l_Lean_Name_append(x_39, x_38);
lean_inc(x_40);
lean_inc(x_5);
x_41 = l_Lean_Environment_contains(x_5, x_40, x_20);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_40);
x_42 = lean_box(0);
x_29 = x_36;
x_30 = x_38;
x_31 = x_37;
x_32 = x_42;
goto block_35;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_40);
x_29 = x_36;
x_30 = x_38;
x_31 = x_37;
x_32 = x_43;
goto block_35;
}
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_56 = !lean_is_exclusive(x_26);
if (x_56 == 0)
{
return x_26;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_26, 0);
x_58 = lean_ctor_get(x_26, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_26);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_dec(x_22);
x_13 = x_7;
x_14 = x_12;
goto block_18;
}
}
else
{
lean_dec(x_22);
x_13 = x_7;
x_14 = x_12;
goto block_18;
}
}
block_18:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_6, 2);
x_16 = lean_nat_add(x_8, x_15);
lean_dec(x_8);
x_7 = x_13;
x_8 = x_16;
x_12 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_getElimExprInfo_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_getElimExprInfo_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_11, x_13, x_14, x_15);
return x_16;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_getElimExprInfo_spec__5_spec__5___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Expr_isFVar(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_getElimExprInfo_spec__5_spec__5___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_23; uint8_t x_24; 
x_23 = lean_array_get_size(x_3);
x_24 = lean_nat_dec_eq(x_23, x_2);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_25 = lean_mk_string_unchecked("expecetd ", 9, 9);
x_26 = l_Lean_stringToMessageData(x_25);
lean_dec(x_25);
x_27 = l___private_Init_Data_Repr_0__Nat_reprFast(x_2);
x_28 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lean_MessageData_ofFormat(x_28);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_mk_string_unchecked(" parameters at motive type, got ", 32, 32);
x_32 = l_Lean_stringToMessageData(x_31);
lean_dec(x_31);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = l___private_Init_Data_Repr_0__Nat_reprFast(x_23);
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = l_Lean_MessageData_ofFormat(x_35);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_mk_string_unchecked(":", 1, 1);
x_39 = l_Lean_stringToMessageData(x_38);
lean_dec(x_38);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_indentExpr(x_1);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_mk_string_unchecked("", 0, 0);
x_44 = l_Lean_stringToMessageData(x_43);
lean_dec(x_43);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_45, x_5, x_6, x_7, x_8, x_9);
return x_46;
}
else
{
lean_dec(x_23);
lean_dec(x_2);
x_10 = x_9;
goto block_22;
}
block_22:
{
uint8_t x_11; 
x_11 = l_Lean_Expr_isSort(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_mk_string_unchecked("motive result type must be a sort", 33, 33);
x_13 = l_Lean_stringToMessageData(x_12);
lean_dec(x_12);
x_14 = l_Lean_indentExpr(x_1);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_mk_string_unchecked("", 0, 0);
x_17 = l_Lean_stringToMessageData(x_16);
lean_dec(x_16);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_18, x_5, x_6, x_7, x_8, x_10);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_10);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_getElimExprInfo_spec__5_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_6) == 5)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_array_set(x_7, x_8, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_8, x_17);
lean_dec(x_8);
x_6 = x_14;
x_7 = x_16;
x_8 = x_18;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_91; 
lean_dec(x_8);
x_20 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_getElimExprInfo_spec__5_spec__5___lam__0___boxed), 1, 0);
x_91 = l_Lean_Expr_isFVar(x_6);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_92 = lean_mk_string_unchecked("expected resulting type of eliminator to be an application of one of its parameters (the motive):", 97, 97);
x_93 = l_Lean_stringToMessageData(x_92);
lean_dec(x_92);
x_94 = l_Lean_indentExpr(x_5);
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_mk_string_unchecked("", 0, 0);
x_97 = l_Lean_stringToMessageData(x_96);
lean_dec(x_96);
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_98, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
return x_99;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_99, 0);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_99);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
else
{
lean_dec(x_5);
x_21 = x_9;
x_22 = x_10;
x_23 = x_11;
x_24 = x_12;
x_25 = x_13;
goto block_90;
}
block_90:
{
lean_object* x_26; 
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_6);
x_26 = lean_infer_type(x_6, x_21, x_22, x_23, x_24, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_array_get_size(x_7);
lean_inc(x_29);
lean_inc(x_27);
x_30 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_getElimExprInfo_spec__5_spec__5___lam__1___boxed), 9, 2);
lean_closure_set(x_30, 0, x_27);
lean_closure_set(x_30, 1, x_29);
x_31 = lean_box(0);
x_32 = lean_unbox(x_31);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_33 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1(lean_box(0), x_27, x_30, x_32, x_21, x_22, x_23, x_24, x_28);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_Array_idxOf_x3f___at___Lean_Meta_getElimExprInfo_spec__0(x_1, x_6);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_29);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_36 = lean_mk_string_unchecked("unexpected eliminator type", 26, 26);
x_37 = l_Lean_stringToMessageData(x_36);
lean_dec(x_36);
x_38 = l_Lean_indentExpr(x_2);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_mk_string_unchecked("", 0, 0);
x_41 = l_Lean_stringToMessageData(x_40);
lean_dec(x_40);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_42, x_21, x_22, x_23, x_24, x_34);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; size_t x_46; lean_object* x_47; size_t x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_35, 0);
lean_inc(x_44);
lean_dec(x_35);
x_45 = l_Array_takeWhile___redArg(x_20, x_7);
x_46 = lean_array_size(x_45);
x_47 = lean_unsigned_to_nat(0u);
x_48 = lean_usize_of_nat(x_47);
lean_inc(x_45);
lean_inc(x_2);
x_49 = l_Array_mapMUnsafe_map___at___Lean_Meta_getElimExprInfo_spec__3(x_1, x_2, x_46, x_48, x_45, x_21, x_22, x_23, x_24, x_34);
lean_dec(x_22);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_st_ref_get(x_24, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_mk_empty_array_with_capacity(x_47);
x_56 = lean_ctor_get(x_53, 0);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_array_get_size(x_1);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_59, 0, x_47);
lean_ctor_set(x_59, 1, x_57);
lean_ctor_set(x_59, 2, x_58);
x_60 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_getElimExprInfo_spec__4___redArg(x_1, x_6, x_45, x_3, x_56, x_59, x_55, x_47, x_21, x_23, x_24, x_54);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_59);
lean_dec(x_6);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = lean_array_get_size(x_45);
lean_dec(x_45);
x_64 = l_Array_toSubarray___redArg(x_7, x_63, x_29);
x_65 = l_Subarray_size___redArg(x_64);
lean_dec(x_64);
x_66 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_66, 0, x_4);
lean_ctor_set(x_66, 1, x_2);
lean_ctor_set(x_66, 2, x_44);
lean_ctor_set(x_66, 3, x_50);
lean_ctor_set(x_66, 4, x_62);
lean_ctor_set(x_66, 5, x_65);
lean_ctor_set(x_60, 0, x_66);
return x_60;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_67 = lean_ctor_get(x_60, 0);
x_68 = lean_ctor_get(x_60, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_60);
x_69 = lean_array_get_size(x_45);
lean_dec(x_45);
x_70 = l_Array_toSubarray___redArg(x_7, x_69, x_29);
x_71 = l_Subarray_size___redArg(x_70);
lean_dec(x_70);
x_72 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_72, 0, x_4);
lean_ctor_set(x_72, 1, x_2);
lean_ctor_set(x_72, 2, x_44);
lean_ctor_set(x_72, 3, x_50);
lean_ctor_set(x_72, 4, x_67);
lean_ctor_set(x_72, 5, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_68);
return x_73;
}
}
else
{
uint8_t x_74; 
lean_dec(x_50);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_29);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_74 = !lean_is_exclusive(x_60);
if (x_74 == 0)
{
return x_60;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_60, 0);
x_76 = lean_ctor_get(x_60, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_60);
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
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_78 = !lean_is_exclusive(x_49);
if (x_78 == 0)
{
return x_49;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_49, 0);
x_80 = lean_ctor_get(x_49, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_49);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_82 = !lean_is_exclusive(x_33);
if (x_82 == 0)
{
return x_33;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_33, 0);
x_84 = lean_ctor_get(x_33, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_33);
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
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_86 = !lean_is_exclusive(x_26);
if (x_86 == 0)
{
return x_26;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_26, 0);
x_88 = lean_ctor_get(x_26, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_26);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_getElimExprInfo_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_6) == 5)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_array_set(x_7, x_8, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_8, x_17);
x_19 = l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_getElimExprInfo_spec__5_spec__5(x_1, x_2, x_3, x_4, x_5, x_14, x_16, x_18, x_9, x_10, x_11, x_12, x_13);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_91; 
x_20 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_getElimExprInfo_spec__5_spec__5___lam__0___boxed), 1, 0);
x_91 = l_Lean_Expr_isFVar(x_6);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_92 = lean_mk_string_unchecked("expected resulting type of eliminator to be an application of one of its parameters (the motive):", 97, 97);
x_93 = l_Lean_stringToMessageData(x_92);
lean_dec(x_92);
x_94 = l_Lean_indentExpr(x_5);
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_mk_string_unchecked("", 0, 0);
x_97 = l_Lean_stringToMessageData(x_96);
lean_dec(x_96);
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_98, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
return x_99;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_99, 0);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_99);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
else
{
lean_dec(x_5);
x_21 = x_9;
x_22 = x_10;
x_23 = x_11;
x_24 = x_12;
x_25 = x_13;
goto block_90;
}
block_90:
{
lean_object* x_26; 
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_6);
x_26 = lean_infer_type(x_6, x_21, x_22, x_23, x_24, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_array_get_size(x_7);
lean_inc(x_29);
lean_inc(x_27);
x_30 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_getElimExprInfo_spec__5_spec__5___lam__1___boxed), 9, 2);
lean_closure_set(x_30, 0, x_27);
lean_closure_set(x_30, 1, x_29);
x_31 = lean_box(0);
x_32 = lean_unbox(x_31);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_33 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1(lean_box(0), x_27, x_30, x_32, x_21, x_22, x_23, x_24, x_28);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_Array_idxOf_x3f___at___Lean_Meta_getElimExprInfo_spec__0(x_1, x_6);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_29);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_36 = lean_mk_string_unchecked("unexpected eliminator type", 26, 26);
x_37 = l_Lean_stringToMessageData(x_36);
lean_dec(x_36);
x_38 = l_Lean_indentExpr(x_2);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_mk_string_unchecked("", 0, 0);
x_41 = l_Lean_stringToMessageData(x_40);
lean_dec(x_40);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_42, x_21, x_22, x_23, x_24, x_34);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; size_t x_46; lean_object* x_47; size_t x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_35, 0);
lean_inc(x_44);
lean_dec(x_35);
x_45 = l_Array_takeWhile___redArg(x_20, x_7);
x_46 = lean_array_size(x_45);
x_47 = lean_unsigned_to_nat(0u);
x_48 = lean_usize_of_nat(x_47);
lean_inc(x_45);
lean_inc(x_2);
x_49 = l_Array_mapMUnsafe_map___at___Lean_Meta_getElimExprInfo_spec__3(x_1, x_2, x_46, x_48, x_45, x_21, x_22, x_23, x_24, x_34);
lean_dec(x_22);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_st_ref_get(x_24, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_mk_empty_array_with_capacity(x_47);
x_56 = lean_ctor_get(x_53, 0);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_array_get_size(x_1);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_59, 0, x_47);
lean_ctor_set(x_59, 1, x_57);
lean_ctor_set(x_59, 2, x_58);
x_60 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_getElimExprInfo_spec__4___redArg(x_1, x_6, x_45, x_3, x_56, x_59, x_55, x_47, x_21, x_23, x_24, x_54);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_59);
lean_dec(x_6);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = lean_array_get_size(x_45);
lean_dec(x_45);
x_64 = l_Array_toSubarray___redArg(x_7, x_63, x_29);
x_65 = l_Subarray_size___redArg(x_64);
lean_dec(x_64);
x_66 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_66, 0, x_4);
lean_ctor_set(x_66, 1, x_2);
lean_ctor_set(x_66, 2, x_44);
lean_ctor_set(x_66, 3, x_50);
lean_ctor_set(x_66, 4, x_62);
lean_ctor_set(x_66, 5, x_65);
lean_ctor_set(x_60, 0, x_66);
return x_60;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_67 = lean_ctor_get(x_60, 0);
x_68 = lean_ctor_get(x_60, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_60);
x_69 = lean_array_get_size(x_45);
lean_dec(x_45);
x_70 = l_Array_toSubarray___redArg(x_7, x_69, x_29);
x_71 = l_Subarray_size___redArg(x_70);
lean_dec(x_70);
x_72 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_72, 0, x_4);
lean_ctor_set(x_72, 1, x_2);
lean_ctor_set(x_72, 2, x_44);
lean_ctor_set(x_72, 3, x_50);
lean_ctor_set(x_72, 4, x_67);
lean_ctor_set(x_72, 5, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_68);
return x_73;
}
}
else
{
uint8_t x_74; 
lean_dec(x_50);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_29);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_74 = !lean_is_exclusive(x_60);
if (x_74 == 0)
{
return x_60;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_60, 0);
x_76 = lean_ctor_get(x_60, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_60);
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
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_78 = !lean_is_exclusive(x_49);
if (x_78 == 0)
{
return x_49;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_49, 0);
x_80 = lean_ctor_get(x_49, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_49);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_82 = !lean_is_exclusive(x_33);
if (x_82 == 0)
{
return x_33;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_33, 0);
x_84 = lean_ctor_get(x_33, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_33);
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
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_86 = !lean_is_exclusive(x_26);
if (x_86 == 0)
{
return x_26;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_26, 0);
x_88 = lean_ctor_get(x_26, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_26);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getElimExprInfo___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_box(0);
x_12 = l_Lean_Expr_sort___override(x_11);
x_13 = l_Lean_Expr_getAppNumArgs(x_5);
lean_inc(x_13);
x_14 = lean_mk_array(x_13, x_12);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_13, x_15);
lean_dec(x_13);
lean_inc(x_5);
x_17 = l_Lean_Expr_withAppAux___at___Lean_Meta_getElimExprInfo_spec__5(x_4, x_1, x_2, x_3, x_5, x_5, x_14, x_16, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getElimExprInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_mk_string_unchecked("Elab", 4, 4);
x_12 = lean_mk_string_unchecked("induction", 9, 9);
x_13 = l_Lean_Name_mkStr2(x_11, x_12);
lean_inc(x_13);
x_14 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_13, x_3, x_4, x_5, x_6, x_10);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_28; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_1);
lean_inc(x_9);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_getElimExprInfo___lam__0___boxed), 10, 3);
lean_closure_set(x_18, 0, x_9);
lean_closure_set(x_18, 1, x_2);
lean_closure_set(x_18, 2, x_1);
x_28 = lean_unbox(x_16);
lean_dec(x_16);
if (x_28 == 0)
{
lean_free_object(x_14);
lean_dec(x_13);
lean_dec(x_1);
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_17;
goto block_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_29 = lean_mk_string_unchecked("eliminator ", 11, 11);
x_30 = l_Lean_stringToMessageData(x_29);
lean_dec(x_29);
x_31 = l_Lean_indentExpr(x_1);
lean_ctor_set_tag(x_14, 7);
lean_ctor_set(x_14, 1, x_31);
lean_ctor_set(x_14, 0, x_30);
x_32 = lean_mk_string_unchecked("\nhas type", 9, 9);
x_33 = l_Lean_stringToMessageData(x_32);
lean_dec(x_32);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_14);
lean_ctor_set(x_34, 1, x_33);
lean_inc(x_9);
x_35 = l_Lean_indentExpr(x_9);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_mk_string_unchecked("", 0, 0);
x_38 = l_Lean_stringToMessageData(x_37);
lean_dec(x_37);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_13, x_39, x_3, x_4, x_5, x_6, x_17);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_41;
goto block_27;
}
block_27:
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = lean_box(0);
x_25 = lean_unbox(x_24);
x_26 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1(lean_box(0), x_9, x_18, x_25, x_19, x_20, x_21, x_22, x_23);
return x_26;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_54; 
x_42 = lean_ctor_get(x_14, 0);
x_43 = lean_ctor_get(x_14, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_14);
lean_inc(x_1);
lean_inc(x_9);
x_44 = lean_alloc_closure((void*)(l_Lean_Meta_getElimExprInfo___lam__0___boxed), 10, 3);
lean_closure_set(x_44, 0, x_9);
lean_closure_set(x_44, 1, x_2);
lean_closure_set(x_44, 2, x_1);
x_54 = lean_unbox(x_42);
lean_dec(x_42);
if (x_54 == 0)
{
lean_dec(x_13);
lean_dec(x_1);
x_45 = x_3;
x_46 = x_4;
x_47 = x_5;
x_48 = x_6;
x_49 = x_43;
goto block_53;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_55 = lean_mk_string_unchecked("eliminator ", 11, 11);
x_56 = l_Lean_stringToMessageData(x_55);
lean_dec(x_55);
x_57 = l_Lean_indentExpr(x_1);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_mk_string_unchecked("\nhas type", 9, 9);
x_60 = l_Lean_stringToMessageData(x_59);
lean_dec(x_59);
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_60);
lean_inc(x_9);
x_62 = l_Lean_indentExpr(x_9);
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_mk_string_unchecked("", 0, 0);
x_65 = l_Lean_stringToMessageData(x_64);
lean_dec(x_64);
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_13, x_66, x_3, x_4, x_5, x_6, x_43);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_45 = x_3;
x_46 = x_4;
x_47 = x_5;
x_48 = x_6;
x_49 = x_68;
goto block_53;
}
block_53:
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_50 = lean_box(0);
x_51 = lean_unbox(x_50);
x_52 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1(lean_box(0), x_9, x_44, x_51, x_45, x_46, x_47, x_48, x_49);
return x_52;
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
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_8);
if (x_69 == 0)
{
return x_8;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_8, 0);
x_71 = lean_ctor_get(x_8, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_8);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___Array_finIdxOf_x3f___at___Array_idxOf_x3f___at___Lean_Meta_getElimExprInfo_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_idxOfAux___at___Array_finIdxOf_x3f___at___Array_idxOf_x3f___at___Lean_Meta_getElimExprInfo_spec__0_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___Array_idxOf_x3f___at___Lean_Meta_getElimExprInfo_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_finIdxOf_x3f___at___Array_idxOf_x3f___at___Lean_Meta_getElimExprInfo_spec__0_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___Lean_Meta_getElimExprInfo_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_idxOf_x3f___at___Lean_Meta_getElimExprInfo_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_getElimExprInfo_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_mapMUnsafe_map___at___Lean_Meta_getElimExprInfo_spec__3(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_getElimExprInfo_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_getElimExprInfo_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_getElimExprInfo_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_getElimExprInfo_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_getElimExprInfo_spec__5_spec__5___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_getElimExprInfo_spec__5_spec__5___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_getElimExprInfo_spec__5_spec__5___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_getElimExprInfo_spec__5_spec__5___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_getElimExprInfo_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_getElimExprInfo_spec__5_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_getElimExprInfo_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Expr_withAppAux___at___Lean_Meta_getElimExprInfo_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getElimExprInfo___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_getElimExprInfo___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getElimInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_mkConstWithFreshMVarLevels(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_getElimExprInfo(x_9, x_2, x_3, x_4, x_5, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Array_contains___at___Lean_Meta_addImplicitTargets_collect_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_nat_dec_eq(x_1, x_6);
lean_dec(x_6);
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
return x_7;
}
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___Lean_Meta_addImplicitTargets_collect_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
size_t x_6; size_t x_7; uint8_t x_8; 
x_6 = lean_usize_of_nat(x_3);
x_7 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_8 = l_Array_anyMUnsafe_any___at___Array_contains___at___Lean_Meta_addImplicitTargets_collect_spec__0_spec__0(x_2, x_1, x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addImplicitTargets_collect(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_17; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_17 = l_Lean_Meta_whnfD(x_3, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 7)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_84; uint8_t x_85; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 2);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_18, sizeof(void*)*3 + 8);
lean_dec(x_18);
x_84 = lean_ctor_get(x_1, 3);
lean_inc(x_84);
x_85 = l_Array_contains___at___Lean_Meta_addImplicitTargets_collect_spec__0(x_84, x_4);
lean_dec(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_20);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_21);
x_87 = lean_box(0);
x_88 = lean_box(0);
x_89 = lean_unbox(x_87);
lean_inc(x_8);
x_90 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_86, x_89, x_88, x_8, x_9, x_10, x_11, x_19);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_expr_instantiate1(x_22, x_91);
lean_dec(x_91);
lean_dec(x_22);
x_94 = lean_unsigned_to_nat(1u);
x_95 = lean_nat_add(x_4, x_94);
lean_dec(x_4);
x_3 = x_93;
x_4 = x_95;
x_12 = x_92;
goto _start;
}
else
{
uint8_t x_97; 
x_97 = l_Lean_BinderInfo_isExplicit(x_23);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_21);
x_99 = lean_box(0);
x_100 = lean_unbox(x_99);
lean_inc(x_8);
x_101 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_98, x_100, x_20, x_8, x_9, x_10, x_11, x_19);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_expr_instantiate1(x_22, x_102);
lean_dec(x_22);
x_105 = lean_unsigned_to_nat(1u);
x_106 = lean_nat_add(x_4, x_105);
lean_dec(x_4);
x_107 = l_Lean_Expr_mvarId_x21(x_102);
x_108 = lean_array_push(x_6, x_107);
x_109 = lean_array_push(x_7, x_102);
x_3 = x_104;
x_4 = x_106;
x_6 = x_108;
x_7 = x_109;
x_12 = x_103;
goto _start;
}
else
{
lean_object* x_111; uint8_t x_112; 
lean_dec(x_20);
x_111 = lean_array_get_size(x_2);
x_112 = lean_nat_dec_lt(x_5, x_111);
lean_dec(x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_113 = lean_mk_string_unchecked("insufficient number of targets for '", 36, 36);
x_114 = l_Lean_stringToMessageData(x_113);
lean_dec(x_113);
x_115 = lean_ctor_get(x_1, 0);
lean_inc(x_115);
lean_dec(x_1);
x_116 = l_Lean_MessageData_ofExpr(x_115);
x_117 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_mk_string_unchecked("'", 1, 1);
x_119 = l_Lean_stringToMessageData(x_118);
lean_dec(x_118);
x_120 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_119);
x_121 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_120, x_8, x_9, x_10, x_11, x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_122 = !lean_is_exclusive(x_121);
if (x_122 == 0)
{
return x_121;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_121, 0);
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_121);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
else
{
x_37 = x_8;
x_38 = x_9;
x_39 = x_10;
x_40 = x_11;
x_41 = x_19;
goto block_83;
}
}
}
block_36:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_expr_instantiate1(x_22, x_24);
lean_dec(x_22);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_4, x_31);
lean_dec(x_4);
x_33 = lean_nat_add(x_5, x_31);
lean_dec(x_5);
x_34 = lean_array_push(x_7, x_24);
x_3 = x_30;
x_4 = x_32;
x_5 = x_33;
x_7 = x_34;
x_8 = x_25;
x_9 = x_26;
x_10 = x_27;
x_11 = x_28;
x_12 = x_29;
goto _start;
}
block_83:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = l_Lean_instInhabitedExpr;
x_43 = lean_array_get(x_42, x_2, x_5);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_43);
x_44 = lean_infer_type(x_43, x_37, x_38, x_39, x_40, x_41);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_45);
lean_inc(x_21);
x_47 = l_Lean_Meta_isExprDefEq(x_21, x_45, x_37, x_38, x_39, x_40, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_unbox(x_48);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_22);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
x_51 = l_Lean_Meta_mkHasTypeButIsExpectedMsg(x_45, x_21, x_37, x_38, x_39, x_40, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_mk_string_unchecked("target", 6, 6);
x_55 = l_Lean_stringToMessageData(x_54);
lean_dec(x_54);
x_56 = l_Lean_indentExpr(x_43);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_mk_string_unchecked("\n", 1, 1);
x_59 = l_Lean_stringToMessageData(x_58);
lean_dec(x_58);
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_52);
x_62 = lean_mk_string_unchecked("", 0, 0);
x_63 = l_Lean_stringToMessageData(x_62);
lean_dec(x_62);
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_64, x_37, x_38, x_39, x_40, x_53);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
return x_65;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_65, 0);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_65);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
else
{
uint8_t x_70; 
lean_dec(x_43);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
x_70 = !lean_is_exclusive(x_51);
if (x_70 == 0)
{
return x_51;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_51, 0);
x_72 = lean_ctor_get(x_51, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_51);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; 
lean_dec(x_45);
lean_dec(x_21);
x_74 = lean_ctor_get(x_47, 1);
lean_inc(x_74);
lean_dec(x_47);
x_24 = x_43;
x_25 = x_37;
x_26 = x_38;
x_27 = x_39;
x_28 = x_40;
x_29 = x_74;
goto block_36;
}
}
else
{
uint8_t x_75; 
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_47);
if (x_75 == 0)
{
return x_47;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_47, 0);
x_77 = lean_ctor_get(x_47, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_47);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_43);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_44);
if (x_79 == 0)
{
return x_44;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_44, 0);
x_81 = lean_ctor_get(x_44, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_44);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
else
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; 
lean_dec(x_18);
lean_dec(x_4);
x_126 = lean_ctor_get(x_17, 1);
lean_inc(x_126);
lean_dec(x_17);
x_127 = lean_array_get_size(x_2);
x_128 = lean_nat_dec_eq(x_5, x_127);
lean_dec(x_127);
lean_dec(x_5);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
lean_dec(x_7);
lean_dec(x_6);
x_129 = lean_mk_string_unchecked("extra targets for '", 19, 19);
x_130 = l_Lean_stringToMessageData(x_129);
lean_dec(x_129);
x_131 = lean_ctor_get(x_1, 0);
lean_inc(x_131);
lean_dec(x_1);
x_132 = l_Lean_MessageData_ofExpr(x_131);
x_133 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_mk_string_unchecked("'", 1, 1);
x_135 = l_Lean_stringToMessageData(x_134);
lean_dec(x_134);
x_136 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_135);
x_137 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_136, x_8, x_9, x_10, x_11, x_126);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_138 = !lean_is_exclusive(x_137);
if (x_138 == 0)
{
return x_137;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_137, 0);
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_137);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_13 = x_126;
goto block_16;
}
}
}
else
{
uint8_t x_142; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_142 = !lean_is_exclusive(x_17);
if (x_142 == 0)
{
return x_17;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_17, 0);
x_144 = lean_ctor_get(x_17, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_17);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_7);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_contains___at___Lean_Meta_addImplicitTargets_collect_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Array_contains___at___Lean_Meta_addImplicitTargets_collect_spec__0_spec__0(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___Lean_Meta_addImplicitTargets_collect_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at___Lean_Meta_addImplicitTargets_collect_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addImplicitTargets_collect___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_addImplicitTargets_collect(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget(x_1, x_2);
x_7 = lean_name_eq(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
else
{
lean_dec(x_2);
return x_5;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__0_spec__0___redArg(x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_unsigned_to_nat(5u);
x_6 = lean_usize_of_nat(x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_usize_of_nat(x_7);
x_9 = lean_usize_shift_left(x_8, x_6);
x_10 = lean_usize_sub(x_9, x_8);
x_11 = lean_usize_land(x_2, x_10);
x_12 = lean_usize_to_nat(x_11);
x_13 = l_Lean_PersistentHashMap_instInhabitedEntry(lean_box(0), lean_box(0), lean_box(0));
x_14 = lean_array_get(x_13, x_4, x_12);
lean_dec(x_12);
lean_dec(x_4);
switch (lean_obj_tag(x_14)) {
case 0:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_name_eq(x_3, x_15);
lean_dec(x_15);
return x_16;
}
case 1:
{
lean_object* x_17; size_t x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_usize_shift_right(x_2, x_6);
x_1 = x_17;
x_2 = x_18;
goto _start;
}
default: 
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_box(0);
x_21 = lean_unbox(x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__0_spec__0___redArg(x_22, x_23, x_3);
lean_dec(x_22);
return x_24;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; uint8_t x_5; 
x_3 = l___private_Lean_Expr_0__Lean_hashMVarId____x40_Lean_Expr___hyg_1984_(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__0___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 7);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg(x_8, x_1);
x_10 = lean_box(x_9);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_13, 7);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg(x_14, x_1);
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0___redArg(x_1, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_addImplicitTargets_spec__4_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_3, x_2);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_4);
x_19 = lean_array_uget(x_1, x_3);
x_20 = l_Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0___redArg(x_19, x_6, x_9);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_box(0);
x_25 = lean_unbox(x_22);
lean_dec(x_22);
if (x_25 == 0)
{
lean_object* x_26; 
lean_inc(x_19);
x_26 = l_Lean_MVarId_getDecl(x_19, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_33; uint8_t x_34; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
lean_dec(x_27);
x_34 = l_Lean_Name_isAnonymous(x_33);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = l_Lean_Name_hasMacroScopes(x_33);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Lean_MVarId_getDecl(x_19, x_5, x_6, x_7, x_8, x_28);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_mk_string_unchecked("failed to infer implicit target ", 32, 32);
x_40 = l_Lean_stringToMessageData(x_39);
lean_dec(x_39);
x_41 = lean_ctor_get(x_37, 0);
lean_inc(x_41);
lean_dec(x_37);
x_42 = l_Lean_MessageData_ofName(x_41);
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_42);
lean_ctor_set(x_20, 0, x_40);
x_43 = lean_mk_string_unchecked("", 0, 0);
x_44 = l_Lean_stringToMessageData(x_43);
lean_dec(x_43);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_20);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_45, x_5, x_6, x_7, x_8, x_38);
return x_46;
}
else
{
uint8_t x_47; 
lean_free_object(x_20);
x_47 = !lean_is_exclusive(x_36);
if (x_47 == 0)
{
return x_36;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_36, 0);
x_49 = lean_ctor_get(x_36, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_36);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_free_object(x_20);
lean_dec(x_19);
goto block_32;
}
}
else
{
lean_dec(x_33);
lean_free_object(x_20);
lean_dec(x_19);
goto block_32;
}
block_32:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_mk_string_unchecked("failed to infer implicit target", 31, 31);
x_30 = l_Lean_stringToMessageData(x_29);
lean_dec(x_29);
x_31 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_30, x_5, x_6, x_7, x_8, x_28);
return x_31;
}
}
else
{
uint8_t x_51; 
lean_free_object(x_20);
lean_dec(x_19);
x_51 = !lean_is_exclusive(x_26);
if (x_51 == 0)
{
return x_26;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_26, 0);
x_53 = lean_ctor_get(x_26, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_26);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_free_object(x_20);
lean_dec(x_19);
x_10 = x_24;
x_11 = x_23;
goto block_16;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_20, 0);
x_56 = lean_ctor_get(x_20, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_20);
x_57 = lean_box(0);
x_58 = lean_unbox(x_55);
lean_dec(x_55);
if (x_58 == 0)
{
lean_object* x_59; 
lean_inc(x_19);
x_59 = l_Lean_MVarId_getDecl(x_19, x_5, x_6, x_7, x_8, x_56);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_66; uint8_t x_67; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_66 = lean_ctor_get(x_60, 0);
lean_inc(x_66);
lean_dec(x_60);
x_67 = l_Lean_Name_isAnonymous(x_66);
if (x_67 == 0)
{
uint8_t x_68; 
x_68 = l_Lean_Name_hasMacroScopes(x_66);
lean_dec(x_66);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = l_Lean_MVarId_getDecl(x_19, x_5, x_6, x_7, x_8, x_61);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_mk_string_unchecked("failed to infer implicit target ", 32, 32);
x_73 = l_Lean_stringToMessageData(x_72);
lean_dec(x_72);
x_74 = lean_ctor_get(x_70, 0);
lean_inc(x_74);
lean_dec(x_70);
x_75 = l_Lean_MessageData_ofName(x_74);
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_mk_string_unchecked("", 0, 0);
x_78 = l_Lean_stringToMessageData(x_77);
lean_dec(x_77);
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_79, x_5, x_6, x_7, x_8, x_71);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_69, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_69, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_83 = x_69;
} else {
 lean_dec_ref(x_69);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
else
{
lean_dec(x_19);
goto block_65;
}
}
else
{
lean_dec(x_66);
lean_dec(x_19);
goto block_65;
}
block_65:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_mk_string_unchecked("failed to infer implicit target", 31, 31);
x_63 = l_Lean_stringToMessageData(x_62);
lean_dec(x_62);
x_64 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_63, x_5, x_6, x_7, x_8, x_61);
return x_64;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_19);
x_85 = lean_ctor_get(x_59, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_59, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_87 = x_59;
} else {
 lean_dec_ref(x_59);
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
lean_dec(x_19);
x_10 = x_57;
x_11 = x_56;
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_addImplicitTargets_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_3, x_2);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_4);
x_19 = lean_array_uget(x_1, x_3);
x_20 = l_Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0___redArg(x_19, x_6, x_9);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_box(0);
x_25 = lean_unbox(x_22);
lean_dec(x_22);
if (x_25 == 0)
{
lean_object* x_26; 
lean_inc(x_19);
x_26 = l_Lean_MVarId_getDecl(x_19, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_33; uint8_t x_34; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
lean_dec(x_27);
x_34 = l_Lean_Name_isAnonymous(x_33);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = l_Lean_Name_hasMacroScopes(x_33);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Lean_MVarId_getDecl(x_19, x_5, x_6, x_7, x_8, x_28);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_mk_string_unchecked("failed to infer implicit target ", 32, 32);
x_40 = l_Lean_stringToMessageData(x_39);
lean_dec(x_39);
x_41 = lean_ctor_get(x_37, 0);
lean_inc(x_41);
lean_dec(x_37);
x_42 = l_Lean_MessageData_ofName(x_41);
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_42);
lean_ctor_set(x_20, 0, x_40);
x_43 = lean_mk_string_unchecked("", 0, 0);
x_44 = l_Lean_stringToMessageData(x_43);
lean_dec(x_43);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_20);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_45, x_5, x_6, x_7, x_8, x_38);
return x_46;
}
else
{
uint8_t x_47; 
lean_free_object(x_20);
x_47 = !lean_is_exclusive(x_36);
if (x_47 == 0)
{
return x_36;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_36, 0);
x_49 = lean_ctor_get(x_36, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_36);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_free_object(x_20);
lean_dec(x_19);
goto block_32;
}
}
else
{
lean_dec(x_33);
lean_free_object(x_20);
lean_dec(x_19);
goto block_32;
}
block_32:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_mk_string_unchecked("failed to infer implicit target", 31, 31);
x_30 = l_Lean_stringToMessageData(x_29);
lean_dec(x_29);
x_31 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_30, x_5, x_6, x_7, x_8, x_28);
return x_31;
}
}
else
{
uint8_t x_51; 
lean_free_object(x_20);
lean_dec(x_19);
x_51 = !lean_is_exclusive(x_26);
if (x_51 == 0)
{
return x_26;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_26, 0);
x_53 = lean_ctor_get(x_26, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_26);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_free_object(x_20);
lean_dec(x_19);
x_10 = x_24;
x_11 = x_23;
goto block_16;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_20, 0);
x_56 = lean_ctor_get(x_20, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_20);
x_57 = lean_box(0);
x_58 = lean_unbox(x_55);
lean_dec(x_55);
if (x_58 == 0)
{
lean_object* x_59; 
lean_inc(x_19);
x_59 = l_Lean_MVarId_getDecl(x_19, x_5, x_6, x_7, x_8, x_56);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_66; uint8_t x_67; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_66 = lean_ctor_get(x_60, 0);
lean_inc(x_66);
lean_dec(x_60);
x_67 = l_Lean_Name_isAnonymous(x_66);
if (x_67 == 0)
{
uint8_t x_68; 
x_68 = l_Lean_Name_hasMacroScopes(x_66);
lean_dec(x_66);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = l_Lean_MVarId_getDecl(x_19, x_5, x_6, x_7, x_8, x_61);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_mk_string_unchecked("failed to infer implicit target ", 32, 32);
x_73 = l_Lean_stringToMessageData(x_72);
lean_dec(x_72);
x_74 = lean_ctor_get(x_70, 0);
lean_inc(x_74);
lean_dec(x_70);
x_75 = l_Lean_MessageData_ofName(x_74);
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_mk_string_unchecked("", 0, 0);
x_78 = l_Lean_stringToMessageData(x_77);
lean_dec(x_77);
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_79, x_5, x_6, x_7, x_8, x_71);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_69, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_69, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_83 = x_69;
} else {
 lean_dec_ref(x_69);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
else
{
lean_dec(x_19);
goto block_65;
}
}
else
{
lean_dec(x_66);
lean_dec(x_19);
goto block_65;
}
block_65:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_mk_string_unchecked("failed to infer implicit target", 31, 31);
x_63 = l_Lean_stringToMessageData(x_62);
lean_dec(x_62);
x_64 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_63, x_5, x_6, x_7, x_8, x_61);
return x_64;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_19);
x_85 = lean_ctor_get(x_59, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_59, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_87 = x_59;
} else {
 lean_dec_ref(x_59);
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
lean_dec(x_19);
x_10 = x_57;
x_11 = x_56;
goto block_16;
}
}
}
block_16:
{
lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_3, x_13);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_addImplicitTargets_spec__4_spec__4(x_1, x_2, x_14, x_10, x_5, x_6, x_7, x_8, x_11);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_addImplicitTargets_spec__6___redArg(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_9 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_8, x_4, x_5);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_addImplicitTargets_spec__6(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_mapMUnsafe_map___at___Lean_Meta_addImplicitTargets_spec__6___redArg(x_1, x_2, x_3, x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addImplicitTargets(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_mk_empty_array_with_capacity(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_10);
x_11 = l_Lean_Meta_addImplicitTargets_collect(x_1, x_2, x_8, x_9, x_9, x_10, x_10, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_box(0);
x_17 = lean_array_size(x_14);
x_18 = lean_usize_of_nat(x_9);
x_19 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_addImplicitTargets_spec__4(x_14, x_17, x_18, x_16, x_3, x_4, x_5, x_6, x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; size_t x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_array_size(x_15);
x_22 = l_Array_mapMUnsafe_map___at___Lean_Meta_addImplicitTargets_spec__6___redArg(x_21, x_18, x_15, x_4, x_20);
lean_dec(x_4);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_15);
lean_dec(x_4);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_19);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_11);
if (x_27 == 0)
{
return x_11;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_11, 0);
x_29 = lean_ctor_get(x_11, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_11);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__0___redArg(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0_spec__0_spec__0(x_1, x_2, x_5, x_4);
lean_dec(x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_isAssigned___at___Lean_Meta_addImplicitTargets_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_addImplicitTargets_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_addImplicitTargets_spec__4_spec__4(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_addImplicitTargets_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_addImplicitTargets_spec__4(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_addImplicitTargets_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l_Array_mapMUnsafe_map___at___Lean_Meta_addImplicitTargets_spec__6___redArg(x_6, x_7, x_3, x_4, x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_addImplicitTargets_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at___Lean_Meta_addImplicitTargets_spec__6(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addImplicitTargets___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_addImplicitTargets(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCustomEliminator() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_1 = lean_box(0);
x_2 = l_Array_empty(lean_box(0));
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_unbox(x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_5);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminator___redArg___lam__0____x40_Lean_Meta_Tactic_ElimInfo___hyg_2292_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Name_reprPrec(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminator___redArg____x40_Lean_Meta_Tactic_ElimInfo___hyg_2292_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_45; uint8_t x_82; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminator___redArg___lam__0____x40_Lean_Meta_Tactic_ElimInfo___hyg_2292_), 1, 0);
x_3 = lean_mk_string_unchecked("{ ", 2, 2);
x_4 = lean_box(0);
x_5 = lean_mk_string_unchecked("induction", 9, 9);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_mk_string_unchecked(" := ", 4, 4);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_inc(x_9);
x_10 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_unsigned_to_nat(13u);
x_12 = lean_nat_to_int(x_11);
x_82 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_mk_string_unchecked("false", 5, 5);
x_84 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_45 = x_84;
goto block_81;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_mk_string_unchecked("true", 4, 4);
x_86 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_45 = x_86;
goto block_81;
}
block_44:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_18 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_15);
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_13);
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
x_23 = lean_mk_string_unchecked("elimName", 8, 8);
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_9);
x_27 = lean_unsigned_to_nat(12u);
x_28 = lean_nat_to_int(x_27);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_Lean_Name_reprPrec(x_29, x_30);
x_32 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_15);
x_34 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_mk_string_unchecked(" }", 2, 2);
x_36 = lean_unsigned_to_nat(2u);
x_37 = lean_nat_to_int(x_36);
x_38 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_38, 0, x_3);
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_34);
x_40 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_40, 0, x_35);
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_15);
return x_43;
}
block_81:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
lean_inc(x_12);
x_46 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_46, 0, x_12);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_48, 0, x_46);
x_49 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_49);
x_50 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_50, 0, x_10);
lean_ctor_set(x_50, 1, x_48);
x_51 = lean_mk_string_unchecked(",", 1, 1);
x_52 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_52, 0, x_51);
lean_inc(x_52);
x_53 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_box(1);
x_55 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_mk_string_unchecked("typeNames", 9, 9);
x_57 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_57);
lean_inc(x_9);
x_59 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_9);
x_60 = lean_ctor_get(x_1, 0);
lean_inc(x_60);
x_61 = lean_array_get_size(x_60);
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_nat_dec_eq(x_61, x_62);
lean_dec(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_64 = lean_mk_string_unchecked("#[", 2, 2);
x_65 = lean_array_to_list(x_60);
lean_inc(x_52);
x_66 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_66, 0, x_52);
lean_ctor_set(x_66, 1, x_54);
x_67 = l_Std_Format_joinSep(lean_box(0), x_2, x_65, x_66);
x_68 = lean_mk_string_unchecked("]", 1, 1);
x_69 = lean_unsigned_to_nat(2u);
x_70 = lean_nat_to_int(x_69);
x_71 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_71, 0, x_64);
x_72 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_67);
x_73 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_73, 0, x_68);
x_74 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_75, 0, x_70);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Std_Format_fill(x_75);
x_77 = lean_unbox(x_47);
x_13 = x_52;
x_14 = x_59;
x_15 = x_77;
x_16 = x_54;
x_17 = x_76;
goto block_44;
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
lean_dec(x_60);
lean_dec(x_2);
x_78 = lean_mk_string_unchecked("#[]", 3, 3);
x_79 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_80 = lean_unbox(x_47);
x_13 = x_52;
x_14 = x_59;
x_15 = x_80;
x_16 = x_54;
x_17 = x_79;
goto block_44;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminator____x40_Lean_Meta_Tactic_ElimInfo___hyg_2292_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminator___redArg____x40_Lean_Meta_Tactic_ElimInfo___hyg_2292_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminator____x40_Lean_Meta_Tactic_ElimInfo___hyg_2292____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminator____x40_Lean_Meta_Tactic_ElimInfo___hyg_2292_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instReprCustomEliminator() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminator____x40_Lean_Meta_Tactic_ElimInfo___hyg_2292____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCustomEliminators() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_1 = lean_box(1);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_shiftl(x_2, x_4);
x_6 = lean_unsigned_to_nat(3u);
x_7 = lean_nat_div(x_5, x_6);
lean_dec(x_5);
x_8 = l_Nat_nextPowerOfTwo(x_7);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = lean_mk_array(x_8, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_unbox(x_1);
lean_ctor_set_uint8(x_14, sizeof(void*)*2, x_15);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_SMap_fold___at___Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
lean_dec(x_3);
lean_inc(x_1);
x_7 = lean_apply_3(x_1, x_2, x_4, x_5);
x_2 = x_7;
x_3 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_SMap_fold___at___Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_SMap_fold___at___Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0_spec__0_spec__0___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_SMap_fold___at___Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_SMap_fold___at___Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0_spec__0_spec__0___redArg(x_1, x_5, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
x_5 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_SMap_fold___at___Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_SMap_fold___at___Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0_spec__0_spec__1___redArg(x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_alloc_closure((void*)(l_instHashableBool___lam__0___boxed), 1, 0);
x_6 = l_Lean_instHashableName;
x_7 = l_instHashableArray___redArg(x_6);
x_8 = lean_alloc_closure((void*)(l_instHashableProd___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_8, 0, x_5);
lean_closure_set(x_8, 1, x_7);
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_10, 1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_11);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
x_15 = l_Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl_spec__0(lean_box(0), x_1, x_8, lean_box(0), lean_box(0), x_9, x_2, x_3);
lean_dec(x_8);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_13, x_13);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_13);
x_17 = l_Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl_spec__0(lean_box(0), x_1, x_8, lean_box(0), lean_box(0), x_9, x_2, x_3);
lean_dec(x_8);
return x_17;
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_usize_of_nat(x_12);
x_19 = lean_usize_of_nat(x_13);
lean_dec(x_13);
lean_inc(x_2);
x_20 = l_Array_foldlMUnsafe_fold___at___Lean_SMap_fold___at___Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0_spec__0_spec__1___redArg(x_2, x_11, x_18, x_19, x_3);
x_21 = l_Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl_spec__0(lean_box(0), x_1, x_8, lean_box(0), lean_box(0), x_9, x_2, x_20);
lean_dec(x_8);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_SMap_fold___at___Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0_spec__0___redArg(x_1, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0___redArg___lam__0), 3, 0);
x_4 = lean_box(0);
x_5 = l_Lean_SMap_fold___at___Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0_spec__0___redArg(x_1, x_3, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__4_spec__4_spec__4___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_28; uint8_t x_53; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_4 = x_1;
} else {
 lean_dec_ref(x_1);
 x_4 = lean_box(0);
}
x_5 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminator___redArg___lam__0____x40_Lean_Meta_Tactic_ElimInfo___hyg_2292_), 1, 0);
x_6 = lean_mk_string_unchecked("(", 1, 1);
x_53 = lean_unbox(x_2);
lean_dec(x_2);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_mk_string_unchecked("false", 5, 5);
x_55 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_28 = x_55;
goto block_52;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_mk_string_unchecked("true", 4, 4);
x_57 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_28 = x_57;
goto block_52;
}
block_27:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
if (lean_is_scalar(x_4)) {
 x_9 = lean_alloc_ctor(1, 2, 0);
} else {
 x_9 = x_4;
 lean_ctor_set_tag(x_9, 1);
}
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l_List_reverse___redArg(x_9);
x_11 = lean_mk_string_unchecked(",", 1, 1);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_box(1);
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(x_10, x_14);
x_16 = lean_mk_string_unchecked(")", 1, 1);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_to_int(x_17);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_6);
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_16);
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_25, 0, x_23);
x_26 = lean_unbox(x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_26);
return x_25;
}
block_52:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_array_get_size(x_3);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_nat_dec_eq(x_31, x_32);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_34 = lean_mk_string_unchecked("#[", 2, 2);
x_35 = lean_array_to_list(x_3);
x_36 = lean_mk_string_unchecked(",", 1, 1);
x_37 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_box(1);
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Std_Format_joinSep(lean_box(0), x_5, x_35, x_39);
x_41 = lean_mk_string_unchecked("]", 1, 1);
x_42 = lean_unsigned_to_nat(2u);
x_43 = lean_nat_to_int(x_42);
x_44 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_44, 0, x_34);
x_45 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
x_46 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_47 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Std_Format_fill(x_48);
x_7 = x_30;
x_8 = x_49;
goto block_27;
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_5);
lean_dec(x_3);
x_50 = lean_mk_string_unchecked("#[]", 3, 3);
x_51 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_7 = x_30;
x_8 = x_51;
goto block_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__4_spec__4_spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Prod_repr___at___Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__4_spec__4_spec__4___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__4_spec__4___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_mk_string_unchecked("(", 1, 1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Prod_repr___at___Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__4_spec__4_spec__4___redArg(x_3);
x_8 = lean_box(0);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_7);
x_9 = l_Lean_Name_reprPrec(x_4, x_6);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_1);
x_11 = l_List_reverse___redArg(x_10);
x_12 = lean_mk_string_unchecked(",", 1, 1);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_box(1);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(x_11, x_15);
x_17 = lean_mk_string_unchecked(")", 1, 1);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_to_int(x_18);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_5);
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_17);
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_26, 0, x_24);
x_27 = lean_unbox(x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_27);
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_1);
x_30 = lean_mk_string_unchecked("(", 1, 1);
x_31 = lean_unsigned_to_nat(0u);
x_32 = l_Prod_repr___at___Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__4_spec__4_spec__4___redArg(x_28);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_Name_reprPrec(x_29, x_31);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_List_reverse___redArg(x_36);
x_38 = lean_mk_string_unchecked(",", 1, 1);
x_39 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_box(1);
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(x_37, x_41);
x_43 = lean_mk_string_unchecked(")", 1, 1);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_to_int(x_44);
x_46 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_46, 0, x_30);
x_47 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_42);
x_48 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_48, 0, x_43);
x_49 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_52, 0, x_50);
x_53 = lean_unbox(x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_53);
return x_52;
}
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__4_spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__4_spec__4___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__4___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__4_spec__4___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__4___redArg(lean_object* x_1) {
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
x_4 = lean_alloc_closure((void*)(l_List_repr___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__4___redArg___lam__0), 1, 0);
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
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_repr___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__4___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators___redArg___lam__0____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408_(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(1);
x_4 = lean_box(0);
if (x_1 == 0)
{
if (x_2 == 0)
{
uint8_t x_5; 
x_5 = lean_unbox(x_3);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
return x_6;
}
}
else
{
if (x_2 == 0)
{
uint8_t x_7; 
x_7 = lean_unbox(x_4);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_unbox(x_3);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators___redArg____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators___redArg___lam__0____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408____boxed), 2, 0);
x_3 = l_Lean_Name_instBEq;
x_4 = lean_alloc_closure((void*)(l_Array_instBEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_mk_string_unchecked("{ ", 2, 2);
x_6 = lean_box(0);
x_7 = lean_mk_string_unchecked("map", 3, 3);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_mk_string_unchecked(" := ", 4, 4);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_unsigned_to_nat(7u);
x_14 = lean_nat_to_int(x_13);
x_15 = l_instBEqOfDecidableEq___redArg(x_2);
x_16 = l_instBEqProd___redArg(x_15, x_4);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0___redArg(x_16, x_1);
lean_dec(x_16);
x_19 = l_List_repr___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__4___redArg(x_18);
x_20 = lean_mk_string_unchecked(".toSMap", 7, 7);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Repr_addAppParen(x_22, x_17);
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_26, 0, x_24);
x_27 = lean_unbox(x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_27);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_12);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_mk_string_unchecked(" }", 2, 2);
x_30 = lean_unsigned_to_nat(2u);
x_31 = lean_nat_to_int(x_30);
x_32 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_32, 0, x_5);
x_33 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_28);
x_34 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_34, 0, x_29);
x_35 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_unbox(x_25);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_38);
return x_37;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators___redArg____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_SMap_fold___at___Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_SMap_fold___at___Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0_spec__0_spec__1___redArg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_SMap_fold___at___Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_foldlMUnsafe_fold___at___Lean_SMap_fold___at___Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_SMap_fold___at___Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_SMap_fold___at___Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_SMap_toList___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__4_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Prod_repr___at___Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__4_spec__4_spec__4(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__4_spec__4(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_repr___at_____private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408__spec__4(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators___redArg___lam__0____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators___redArg___lam__0____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators___redArg____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators___redArg____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408_(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instReprCustomEliminators() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT uint64_t l_Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, uint64_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Name_hash___override(x_6);
lean_dec(x_6);
x_8 = lean_uint64_mix_hash(x_4, x_7);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_19; uint8_t x_30; 
x_5 = lean_alloc_closure((void*)(l_instHashableBool___lam__0___boxed), 1, 0);
x_6 = l_Lean_instHashableName;
x_7 = l_instHashableArray___redArg(x_6);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_instHashableProd___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_10, 0, x_5);
lean_closure_set(x_10, 1, x_7);
x_30 = lean_unbox(x_8);
lean_dec(x_8);
if (x_30 == 0)
{
lean_object* x_31; uint64_t x_32; 
x_31 = lean_unsigned_to_nat(13u);
x_32 = lean_uint64_of_nat(x_31);
x_19 = x_32;
goto block_29;
}
else
{
lean_object* x_33; uint64_t x_34; 
x_33 = lean_unsigned_to_nat(11u);
x_34 = lean_uint64_of_nat(x_33);
x_19 = x_34;
goto block_29;
}
block_18:
{
uint64_t x_13; size_t x_14; lean_object* x_15; size_t x_16; lean_object* x_17; 
x_13 = lean_uint64_mix_hash(x_11, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert_spec__0___redArg(x_1, x_10, x_2, x_14, x_16, x_3, x_4);
return x_17;
}
block_29:
{
lean_object* x_20; uint64_t x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_unsigned_to_nat(7u);
x_21 = lean_uint64_of_nat(x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_array_get_size(x_9);
x_24 = lean_nat_dec_lt(x_22, x_23);
if (x_24 == 0)
{
lean_dec(x_23);
lean_dec(x_9);
x_11 = x_19;
x_12 = x_21;
goto block_18;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_23, x_23);
if (x_25 == 0)
{
lean_dec(x_23);
lean_dec(x_9);
x_11 = x_19;
x_12 = x_21;
goto block_18;
}
else
{
size_t x_26; size_t x_27; uint64_t x_28; 
x_26 = lean_usize_of_nat(x_22);
x_27 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_28 = l_Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__0(x_9, x_26, x_27, x_21);
lean_dec(x_9);
x_11 = x_19;
x_12 = x_28;
goto block_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_8 = lean_apply_2(x_1, x_6, x_2);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
x_3 = x_7;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__3_spec__3_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; uint64_t x_30; uint8_t x_44; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_6 = x_2;
} else {
 lean_dec_ref(x_2);
 x_6 = lean_box(0);
}
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
x_9 = lean_array_get_size(x_1);
x_44 = lean_unbox(x_7);
lean_dec(x_7);
if (x_44 == 0)
{
lean_object* x_45; uint64_t x_46; 
x_45 = lean_unsigned_to_nat(13u);
x_46 = lean_uint64_of_nat(x_45);
x_30 = x_46;
goto block_43;
}
else
{
lean_object* x_47; uint64_t x_48; 
x_47 = lean_unsigned_to_nat(11u);
x_48 = lean_uint64_of_nat(x_47);
x_30 = x_48;
goto block_43;
}
block_29:
{
lean_object* x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; size_t x_19; size_t x_20; lean_object* x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_11 = lean_unsigned_to_nat(32u);
x_12 = lean_uint64_of_nat(x_11);
x_13 = lean_uint64_shift_right(x_10, x_12);
x_14 = lean_uint64_xor(x_10, x_13);
x_15 = lean_unsigned_to_nat(16u);
x_16 = lean_uint64_of_nat(x_15);
x_17 = lean_uint64_shift_right(x_14, x_16);
x_18 = lean_uint64_xor(x_14, x_17);
x_19 = lean_uint64_to_usize(x_18);
x_20 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_usize_of_nat(x_21);
x_23 = lean_usize_sub(x_20, x_22);
x_24 = lean_usize_land(x_19, x_23);
x_25 = lean_array_uget(x_1, x_24);
if (lean_is_scalar(x_6)) {
 x_26 = lean_alloc_ctor(1, 3, 0);
} else {
 x_26 = x_6;
}
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_4);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_array_uset(x_1, x_24, x_26);
x_1 = x_27;
x_2 = x_5;
goto _start;
}
block_43:
{
lean_object* x_31; uint64_t x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_unsigned_to_nat(7u);
x_32 = lean_uint64_of_nat(x_31);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_array_get_size(x_8);
x_35 = lean_nat_dec_lt(x_33, x_34);
if (x_35 == 0)
{
uint64_t x_36; 
lean_dec(x_34);
lean_dec(x_8);
x_36 = lean_uint64_mix_hash(x_30, x_32);
x_10 = x_36;
goto block_29;
}
else
{
uint8_t x_37; 
x_37 = lean_nat_dec_le(x_34, x_34);
if (x_37 == 0)
{
uint64_t x_38; 
lean_dec(x_34);
lean_dec(x_8);
x_38 = lean_uint64_mix_hash(x_30, x_32);
x_10 = x_38;
goto block_29;
}
else
{
size_t x_39; size_t x_40; uint64_t x_41; uint64_t x_42; 
x_39 = lean_usize_of_nat(x_33);
x_40 = lean_usize_of_nat(x_34);
lean_dec(x_34);
x_41 = l_Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__0(x_8, x_39, x_40, x_32);
lean_dec(x_8);
x_42 = lean_uint64_mix_hash(x_30, x_41);
x_10 = x_42;
goto block_29;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__3_spec__3_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__3_spec__3_spec__3_spec__3___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__3_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; uint64_t x_30; uint8_t x_44; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_6 = x_2;
} else {
 lean_dec_ref(x_2);
 x_6 = lean_box(0);
}
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
x_9 = lean_array_get_size(x_1);
x_44 = lean_unbox(x_7);
lean_dec(x_7);
if (x_44 == 0)
{
lean_object* x_45; uint64_t x_46; 
x_45 = lean_unsigned_to_nat(13u);
x_46 = lean_uint64_of_nat(x_45);
x_30 = x_46;
goto block_43;
}
else
{
lean_object* x_47; uint64_t x_48; 
x_47 = lean_unsigned_to_nat(11u);
x_48 = lean_uint64_of_nat(x_47);
x_30 = x_48;
goto block_43;
}
block_29:
{
lean_object* x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; size_t x_19; size_t x_20; lean_object* x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_11 = lean_unsigned_to_nat(32u);
x_12 = lean_uint64_of_nat(x_11);
x_13 = lean_uint64_shift_right(x_10, x_12);
x_14 = lean_uint64_xor(x_10, x_13);
x_15 = lean_unsigned_to_nat(16u);
x_16 = lean_uint64_of_nat(x_15);
x_17 = lean_uint64_shift_right(x_14, x_16);
x_18 = lean_uint64_xor(x_14, x_17);
x_19 = lean_uint64_to_usize(x_18);
x_20 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_usize_of_nat(x_21);
x_23 = lean_usize_sub(x_20, x_22);
x_24 = lean_usize_land(x_19, x_23);
x_25 = lean_array_uget(x_1, x_24);
if (lean_is_scalar(x_6)) {
 x_26 = lean_alloc_ctor(1, 3, 0);
} else {
 x_26 = x_6;
}
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_4);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_array_uset(x_1, x_24, x_26);
x_28 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__3_spec__3_spec__3_spec__3___redArg(x_27, x_5);
return x_28;
}
block_43:
{
lean_object* x_31; uint64_t x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_unsigned_to_nat(7u);
x_32 = lean_uint64_of_nat(x_31);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_array_get_size(x_8);
x_35 = lean_nat_dec_lt(x_33, x_34);
if (x_35 == 0)
{
uint64_t x_36; 
lean_dec(x_34);
lean_dec(x_8);
x_36 = lean_uint64_mix_hash(x_30, x_32);
x_10 = x_36;
goto block_29;
}
else
{
uint8_t x_37; 
x_37 = lean_nat_dec_le(x_34, x_34);
if (x_37 == 0)
{
uint64_t x_38; 
lean_dec(x_34);
lean_dec(x_8);
x_38 = lean_uint64_mix_hash(x_30, x_32);
x_10 = x_38;
goto block_29;
}
else
{
size_t x_39; size_t x_40; uint64_t x_41; uint64_t x_42; 
x_39 = lean_usize_of_nat(x_33);
x_40 = lean_usize_of_nat(x_34);
lean_dec(x_34);
x_41 = l_Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__0(x_8, x_39, x_40, x_32);
lean_dec(x_8);
x_42 = lean_uint64_mix_hash(x_30, x_41);
x_10 = x_42;
goto block_29;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__3_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__3_spec__3_spec__3___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__3_spec__3_spec__3___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__3_spec__3___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__3___redArg(lean_object* x_1) {
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
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__3_spec__3___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__3___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_4, 2);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_6);
x_9 = lean_apply_2(x_1, x_6, x_2);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__7___redArg(x_1, x_2, x_3, x_8);
lean_ctor_set(x_4, 2, x_11);
return x_4;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 0, x_2);
return x_4;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_ctor_get(x_4, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_12);
x_15 = lean_apply_2(x_1, x_12, x_2);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__7___redArg(x_1, x_2, x_3, x_14);
x_18 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_17);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_3);
lean_ctor_set(x_19, 2, x_14);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__7___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 1);
x_8 = l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0___redArg(x_1, x_7, x_3, x_4);
lean_ctor_set(x_2, 1, x_8);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_11 = l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0___redArg(x_1, x_10, x_3, x_4);
x_12 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_5);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint64_t x_22; uint64_t x_23; uint64_t x_62; uint8_t x_73; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_15 = x_2;
} else {
 lean_dec_ref(x_2);
 x_15 = lean_box(0);
}
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_18 = x_13;
} else {
 lean_dec_ref(x_13);
 x_18 = lean_box(0);
}
x_19 = lean_ctor_get(x_3, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
x_21 = lean_array_get_size(x_17);
x_73 = lean_unbox(x_19);
lean_dec(x_19);
if (x_73 == 0)
{
lean_object* x_74; uint64_t x_75; 
x_74 = lean_unsigned_to_nat(13u);
x_75 = lean_uint64_of_nat(x_74);
x_62 = x_75;
goto block_72;
}
else
{
lean_object* x_76; uint64_t x_77; 
x_76 = lean_unsigned_to_nat(11u);
x_77 = lean_uint64_of_nat(x_76);
x_62 = x_77;
goto block_72;
}
block_61:
{
uint64_t x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; lean_object* x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; lean_object* x_35; size_t x_36; size_t x_37; size_t x_38; lean_object* x_39; uint8_t x_40; 
x_24 = lean_uint64_mix_hash(x_22, x_23);
x_25 = lean_unsigned_to_nat(32u);
x_26 = lean_uint64_of_nat(x_25);
x_27 = lean_uint64_shift_right(x_24, x_26);
x_28 = lean_uint64_xor(x_24, x_27);
x_29 = lean_unsigned_to_nat(16u);
x_30 = lean_uint64_of_nat(x_29);
x_31 = lean_uint64_shift_right(x_28, x_30);
x_32 = lean_uint64_xor(x_28, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_usize_of_nat(x_35);
x_37 = lean_usize_sub(x_34, x_36);
x_38 = lean_usize_land(x_33, x_37);
x_39 = lean_array_uget(x_17, x_38);
lean_inc(x_39);
lean_inc(x_3);
lean_inc(x_1);
x_40 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2___redArg(x_1, x_3, x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_1);
x_41 = lean_nat_add(x_16, x_35);
lean_dec(x_16);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_3);
lean_ctor_set(x_42, 1, x_4);
lean_ctor_set(x_42, 2, x_39);
x_43 = lean_array_uset(x_17, x_38, x_42);
x_44 = lean_unsigned_to_nat(2u);
x_45 = lean_nat_shiftl(x_41, x_44);
x_46 = lean_unsigned_to_nat(3u);
x_47 = lean_nat_div(x_45, x_46);
lean_dec(x_45);
x_48 = lean_array_get_size(x_43);
x_49 = lean_nat_dec_le(x_47, x_48);
lean_dec(x_48);
lean_dec(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__3___redArg(x_43);
if (lean_is_scalar(x_18)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_18;
}
lean_ctor_set(x_51, 0, x_41);
lean_ctor_set(x_51, 1, x_50);
if (lean_is_scalar(x_15)) {
 x_52 = lean_alloc_ctor(0, 2, 1);
} else {
 x_52 = x_15;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_14);
lean_ctor_set_uint8(x_52, sizeof(void*)*2, x_5);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; 
if (lean_is_scalar(x_18)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_18;
}
lean_ctor_set(x_53, 0, x_41);
lean_ctor_set(x_53, 1, x_43);
if (lean_is_scalar(x_15)) {
 x_54 = lean_alloc_ctor(0, 2, 1);
} else {
 x_54 = x_15;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_14);
lean_ctor_set_uint8(x_54, sizeof(void*)*2, x_5);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_55 = lean_box(0);
x_56 = lean_array_uset(x_17, x_38, x_55);
x_57 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__7___redArg(x_1, x_3, x_4, x_39);
x_58 = lean_array_uset(x_56, x_38, x_57);
if (lean_is_scalar(x_18)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_18;
}
lean_ctor_set(x_59, 0, x_16);
lean_ctor_set(x_59, 1, x_58);
if (lean_is_scalar(x_15)) {
 x_60 = lean_alloc_ctor(0, 2, 1);
} else {
 x_60 = x_15;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_14);
lean_ctor_set_uint8(x_60, sizeof(void*)*2, x_5);
return x_60;
}
}
block_72:
{
lean_object* x_63; uint64_t x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_63 = lean_unsigned_to_nat(7u);
x_64 = lean_uint64_of_nat(x_63);
x_65 = lean_unsigned_to_nat(0u);
x_66 = lean_array_get_size(x_20);
x_67 = lean_nat_dec_lt(x_65, x_66);
if (x_67 == 0)
{
lean_dec(x_66);
lean_dec(x_20);
x_22 = x_62;
x_23 = x_64;
goto block_61;
}
else
{
uint8_t x_68; 
x_68 = lean_nat_dec_le(x_66, x_66);
if (x_68 == 0)
{
lean_dec(x_66);
lean_dec(x_20);
x_22 = x_62;
x_23 = x_64;
goto block_61;
}
else
{
size_t x_69; size_t x_70; uint64_t x_71; 
x_69 = lean_usize_of_nat(x_65);
x_70 = lean_usize_of_nat(x_66);
lean_dec(x_66);
x_71 = l_Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__0(x_20, x_69, x_70, x_64);
lean_dec(x_20);
x_22 = x_62;
x_23 = x_71;
goto block_61;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addCustomEliminatorEntry(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators___redArg___lam__0____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408____boxed), 2, 0);
x_4 = l_Lean_Name_instBEq;
x_5 = lean_alloc_closure((void*)(l_Array_instBEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = l_instBEqOfDecidableEq___redArg(x_3);
x_7 = l_instBEqProd___redArg(x_6, x_5);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_box(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = l_Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0___redArg(x_7, x_1, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__0(x_1, x_5, x_6, x_7);
lean_dec(x_1);
x_9 = lean_box_uint64(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__2(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___Lean_Meta_initFn____x40_Lean_Meta_Tactic_ElimInfo___hyg_2474__spec__0___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___Lean_Meta_initFn____x40_Lean_Meta_Tactic_ElimInfo___hyg_2474__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_SMap_switch___at___Lean_Meta_initFn____x40_Lean_Meta_Tactic_ElimInfo___hyg_2474__spec__0___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Tactic_ElimInfo___hyg_2474_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SMap_switch___at___Lean_Meta_initFn____x40_Lean_Meta_Tactic_ElimInfo___hyg_2474__spec__0___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_ElimInfo___hyg_2474_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Meta", 4, 4);
x_4 = lean_mk_string_unchecked("customEliminatorExt", 19, 19);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_addCustomEliminatorEntry), 2, 0);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Tactic_ElimInfo___hyg_2474____boxed), 1, 0);
x_8 = lean_box(1);
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
x_19 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_unbox(x_8);
lean_ctor_set_uint8(x_21, sizeof(void*)*2, x_22);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_6);
lean_ctor_set(x_23, 2, x_21);
lean_ctor_set(x_23, 3, x_7);
x_24 = l_Lean_registerSimpleScopedEnvExtension___redArg(x_23, x_1);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___Lean_Meta_initFn____x40_Lean_Meta_Tactic_ElimInfo___hyg_2474__spec__0___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SMap_switch___at___Lean_Meta_initFn____x40_Lean_Meta_Tactic_ElimInfo___hyg_2474__spec__0___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___Lean_Meta_initFn____x40_Lean_Meta_Tactic_ElimInfo___hyg_2474__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_SMap_switch___at___Lean_Meta_initFn____x40_Lean_Meta_Tactic_ElimInfo___hyg_2474__spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Tactic_ElimInfo___hyg_2474____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Tactic_ElimInfo___hyg_2474_(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___Lean_Meta_mkCustomEliminator_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_27; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_33 = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__0___boxed), 1, 0);
x_34 = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_34, 0, x_2);
x_35 = lean_ctor_get(x_7, 0);
lean_inc(x_35);
lean_dec(x_7);
x_36 = lean_unsigned_to_nat(8u);
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_unsigned_to_nat(2u);
x_39 = lean_nat_shiftl(x_36, x_38);
x_40 = lean_unsigned_to_nat(3u);
x_41 = lean_nat_div(x_39, x_40);
lean_dec(x_39);
x_42 = l_Nat_nextPowerOfTwo(x_41);
lean_dec(x_41);
x_43 = lean_box(0);
x_44 = lean_mk_array(x_42, x_43);
lean_ctor_set(x_5, 1, x_44);
lean_ctor_set(x_5, 0, x_37);
lean_inc(x_35);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_5);
lean_ctor_set(x_45, 1, x_35);
x_46 = l_Lean_Expr_hasFVar(x_1);
if (x_46 == 0)
{
uint8_t x_47; 
x_47 = l_Lean_Expr_hasMVar(x_1);
if (x_47 == 0)
{
lean_dec(x_45);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_1);
x_9 = x_47;
x_10 = x_35;
goto block_26;
}
else
{
lean_object* x_48; 
lean_dec(x_35);
x_48 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_34, x_33, x_1, x_45);
x_27 = x_48;
goto block_32;
}
}
else
{
lean_object* x_49; 
lean_dec(x_35);
x_49 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_34, x_33, x_1, x_45);
x_27 = x_49;
goto block_32;
}
block_26:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_11 = lean_st_ref_take(x_3, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_12, 4);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_15);
lean_ctor_set(x_18, 3, x_16);
lean_ctor_set(x_18, 4, x_17);
x_19 = lean_st_ref_set(x_3, x_18, x_13);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = lean_box(x_9);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_box(x_9);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
block_32:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_unbox(x_29);
lean_dec(x_29);
x_9 = x_31;
x_10 = x_30;
goto block_26;
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_68; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_50 = lean_ctor_get(x_5, 0);
x_51 = lean_ctor_get(x_5, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_5);
x_74 = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__0___boxed), 1, 0);
x_75 = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_75, 0, x_2);
x_76 = lean_ctor_get(x_50, 0);
lean_inc(x_76);
lean_dec(x_50);
x_77 = lean_unsigned_to_nat(8u);
x_78 = lean_unsigned_to_nat(0u);
x_79 = lean_unsigned_to_nat(2u);
x_80 = lean_nat_shiftl(x_77, x_79);
x_81 = lean_unsigned_to_nat(3u);
x_82 = lean_nat_div(x_80, x_81);
lean_dec(x_80);
x_83 = l_Nat_nextPowerOfTwo(x_82);
lean_dec(x_82);
x_84 = lean_box(0);
x_85 = lean_mk_array(x_83, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_78);
lean_ctor_set(x_86, 1, x_85);
lean_inc(x_76);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_76);
x_88 = l_Lean_Expr_hasFVar(x_1);
if (x_88 == 0)
{
uint8_t x_89; 
x_89 = l_Lean_Expr_hasMVar(x_1);
if (x_89 == 0)
{
lean_dec(x_87);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_1);
x_52 = x_89;
x_53 = x_76;
goto block_67;
}
else
{
lean_object* x_90; 
lean_dec(x_76);
x_90 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_75, x_74, x_1, x_87);
x_68 = x_90;
goto block_73;
}
}
else
{
lean_object* x_91; 
lean_dec(x_76);
x_91 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_75, x_74, x_1, x_87);
x_68 = x_91;
goto block_73;
}
block_67:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_54 = lean_st_ref_take(x_3, x_51);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_55, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_55, 3);
lean_inc(x_59);
x_60 = lean_ctor_get(x_55, 4);
lean_inc(x_60);
lean_dec(x_55);
x_61 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_61, 0, x_53);
lean_ctor_set(x_61, 1, x_57);
lean_ctor_set(x_61, 2, x_58);
lean_ctor_set(x_61, 3, x_59);
lean_ctor_set(x_61, 4, x_60);
x_62 = lean_st_ref_set(x_3, x_61, x_56);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
x_65 = lean_box(x_52);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
block_73:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_unbox(x_70);
lean_dec(x_70);
x_52 = x_72;
x_53 = x_71;
goto block_67;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___Lean_Meta_mkCustomEliminator_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_exprDependsOn___at___Lean_Meta_mkCustomEliminator_spec__0___redArg(x_1, x_2, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_nat_dec_lt(x_6, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
x_15 = l_Lean_instInhabitedExpr;
x_16 = lean_array_fget(x_1, x_6);
x_17 = lean_array_get(x_15, x_2, x_16);
lean_dec(x_16);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_18 = lean_infer_type(x_17, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Expr_fvarId_x21(x_3);
x_22 = l_Lean_exprDependsOn___at___Lean_Meta_mkCustomEliminator_spec__0___redArg(x_19, x_21, x_8, x_20);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = lean_box(0);
x_27 = lean_unbox(x_24);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_free_object(x_22);
lean_dec(x_24);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
x_30 = lean_ctor_get(x_4, 2);
x_31 = lean_nat_add(x_6, x_30);
lean_dec(x_6);
x_5 = x_29;
x_6 = x_31;
x_11 = x_25;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_24);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_26);
lean_ctor_set(x_22, 0, x_34);
return x_22;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_22, 0);
x_36 = lean_ctor_get(x_22, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_22);
x_37 = lean_box(0);
x_38 = lean_unbox(x_35);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_35);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
x_41 = lean_ctor_get(x_4, 2);
x_42 = lean_nat_add(x_6, x_41);
lean_dec(x_6);
x_5 = x_40;
x_6 = x_42;
x_11 = x_36;
goto _start;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_35);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_37);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_36);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_47 = !lean_is_exclusive(x_18);
if (x_47 == 0)
{
return x_18;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_18, 0);
x_49 = lean_ctor_get(x_18, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_18);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2_spec__2___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_9 = lean_mk_string_unchecked("unexpected eliminator target type", 33, 33);
x_10 = l_Lean_stringToMessageData(x_9);
lean_dec(x_9);
x_11 = l_Lean_indentExpr(x_1);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_mk_string_unchecked("", 0, 0);
x_14 = l_Lean_stringToMessageData(x_13);
lean_dec(x_13);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_15, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_18; lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_4, 1);
x_25 = lean_nat_dec_lt(x_6, x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_11);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = l_Lean_instInhabitedExpr;
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_array_fget(x_1, x_6);
x_30 = lean_array_get(x_27, x_2, x_29);
lean_dec(x_29);
x_31 = lean_nat_add(x_6, x_28);
lean_inc(x_3);
lean_inc(x_31);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_3);
lean_ctor_set(x_32, 2, x_28);
x_33 = lean_box(0);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_36 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__1___redArg(x_1, x_2, x_30, x_32, x_35, x_31, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_32);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_97; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_97 = lean_ctor_get(x_37, 0);
lean_inc(x_97);
lean_dec(x_37);
if (lean_obj_tag(x_97) == 0)
{
goto block_96;
}
else
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec(x_97);
x_99 = lean_unbox(x_98);
lean_dec(x_98);
if (x_99 == 0)
{
goto block_96;
}
else
{
lean_dec(x_30);
x_12 = x_5;
x_13 = x_38;
goto block_17;
}
}
block_96:
{
lean_object* x_39; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_39 = lean_infer_type(x_30, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Expr_getAppFn(x_40);
switch (lean_obj_tag(x_42)) {
case 0:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_6);
lean_dec(x_3);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec(x_42);
x_44 = l_Lean_Expr_bvar___override(x_43);
x_45 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2_spec__2___redArg___lam__0(x_40, x_5, x_44, x_7, x_8, x_9, x_10, x_41);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_44);
lean_dec(x_5);
x_18 = x_45;
goto block_23;
}
case 1:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_6);
lean_dec(x_3);
x_46 = lean_ctor_get(x_42, 0);
lean_inc(x_46);
lean_dec(x_42);
x_47 = l_Lean_Expr_fvar___override(x_46);
x_48 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2_spec__2___redArg___lam__0(x_40, x_5, x_47, x_7, x_8, x_9, x_10, x_41);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_47);
lean_dec(x_5);
x_18 = x_48;
goto block_23;
}
case 2:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_6);
lean_dec(x_3);
x_49 = lean_ctor_get(x_42, 0);
lean_inc(x_49);
lean_dec(x_42);
x_50 = l_Lean_Expr_mvar___override(x_49);
x_51 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2_spec__2___redArg___lam__0(x_40, x_5, x_50, x_7, x_8, x_9, x_10, x_41);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_50);
lean_dec(x_5);
x_18 = x_51;
goto block_23;
}
case 3:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_6);
lean_dec(x_3);
x_52 = lean_ctor_get(x_42, 0);
lean_inc(x_52);
lean_dec(x_42);
x_53 = l_Lean_Expr_sort___override(x_52);
x_54 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2_spec__2___redArg___lam__0(x_40, x_5, x_53, x_7, x_8, x_9, x_10, x_41);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_53);
lean_dec(x_5);
x_18 = x_54;
goto block_23;
}
case 4:
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_40);
x_55 = lean_ctor_get(x_42, 0);
lean_inc(x_55);
lean_dec(x_42);
x_56 = lean_array_push(x_5, x_55);
x_12 = x_56;
x_13 = x_41;
goto block_17;
}
case 5:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_6);
lean_dec(x_3);
x_57 = lean_ctor_get(x_42, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_42, 1);
lean_inc(x_58);
lean_dec(x_42);
x_59 = l_Lean_Expr_app___override(x_57, x_58);
x_60 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2_spec__2___redArg___lam__0(x_40, x_5, x_59, x_7, x_8, x_9, x_10, x_41);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_59);
lean_dec(x_5);
x_18 = x_60;
goto block_23;
}
case 6:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_6);
lean_dec(x_3);
x_61 = lean_ctor_get(x_42, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_42, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_42, 2);
lean_inc(x_63);
x_64 = lean_ctor_get_uint8(x_42, sizeof(void*)*3 + 8);
lean_dec(x_42);
x_65 = l_Lean_Expr_lam___override(x_61, x_62, x_63, x_64);
x_66 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2_spec__2___redArg___lam__0(x_40, x_5, x_65, x_7, x_8, x_9, x_10, x_41);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_65);
lean_dec(x_5);
x_18 = x_66;
goto block_23;
}
case 7:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_6);
lean_dec(x_3);
x_67 = lean_ctor_get(x_42, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_42, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_42, 2);
lean_inc(x_69);
x_70 = lean_ctor_get_uint8(x_42, sizeof(void*)*3 + 8);
lean_dec(x_42);
x_71 = l_Lean_Expr_forallE___override(x_67, x_68, x_69, x_70);
x_72 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2_spec__2___redArg___lam__0(x_40, x_5, x_71, x_7, x_8, x_9, x_10, x_41);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_71);
lean_dec(x_5);
x_18 = x_72;
goto block_23;
}
case 8:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_6);
lean_dec(x_3);
x_73 = lean_ctor_get(x_42, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_42, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_42, 2);
lean_inc(x_75);
x_76 = lean_ctor_get(x_42, 3);
lean_inc(x_76);
x_77 = lean_ctor_get_uint8(x_42, sizeof(void*)*4 + 8);
lean_dec(x_42);
x_78 = l_Lean_Expr_letE___override(x_73, x_74, x_75, x_76, x_77);
x_79 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2_spec__2___redArg___lam__0(x_40, x_5, x_78, x_7, x_8, x_9, x_10, x_41);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_78);
lean_dec(x_5);
x_18 = x_79;
goto block_23;
}
case 9:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_6);
lean_dec(x_3);
x_80 = lean_ctor_get(x_42, 0);
lean_inc(x_80);
lean_dec(x_42);
x_81 = l_Lean_Expr_lit___override(x_80);
x_82 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2_spec__2___redArg___lam__0(x_40, x_5, x_81, x_7, x_8, x_9, x_10, x_41);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_81);
lean_dec(x_5);
x_18 = x_82;
goto block_23;
}
case 10:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_6);
lean_dec(x_3);
x_83 = lean_ctor_get(x_42, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_42, 1);
lean_inc(x_84);
lean_dec(x_42);
x_85 = l_Lean_Expr_mdata___override(x_83, x_84);
x_86 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2_spec__2___redArg___lam__0(x_40, x_5, x_85, x_7, x_8, x_9, x_10, x_41);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_85);
lean_dec(x_5);
x_18 = x_86;
goto block_23;
}
default: 
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_6);
lean_dec(x_3);
x_87 = lean_ctor_get(x_42, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_42, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_42, 2);
lean_inc(x_89);
lean_dec(x_42);
x_90 = l_Lean_Expr_proj___override(x_87, x_88, x_89);
x_91 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2_spec__2___redArg___lam__0(x_40, x_5, x_90, x_7, x_8, x_9, x_10, x_41);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_90);
lean_dec(x_5);
x_18 = x_91;
goto block_23;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_92 = !lean_is_exclusive(x_39);
if (x_92 == 0)
{
return x_39;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_39, 0);
x_94 = lean_ctor_get(x_39, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_39);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_30);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_100 = !lean_is_exclusive(x_36);
if (x_100 == 0)
{
return x_36;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_36, 0);
x_102 = lean_ctor_get(x_36, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_36);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
block_17:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_4, 2);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_5 = x_12;
x_6 = x_15;
x_11 = x_13;
goto _start;
}
block_23:
{
uint8_t x_19; 
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_18; lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_4, 1);
x_25 = lean_nat_dec_lt(x_6, x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_11);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = l_Lean_instInhabitedExpr;
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_array_fget(x_1, x_6);
x_30 = lean_array_get(x_27, x_2, x_29);
lean_dec(x_29);
x_31 = lean_nat_add(x_6, x_28);
lean_inc(x_3);
lean_inc(x_31);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_3);
lean_ctor_set(x_32, 2, x_28);
x_33 = lean_box(0);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_36 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__1___redArg(x_1, x_2, x_30, x_32, x_35, x_31, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_32);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_97; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_97 = lean_ctor_get(x_37, 0);
lean_inc(x_97);
lean_dec(x_37);
if (lean_obj_tag(x_97) == 0)
{
goto block_96;
}
else
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec(x_97);
x_99 = lean_unbox(x_98);
lean_dec(x_98);
if (x_99 == 0)
{
goto block_96;
}
else
{
lean_dec(x_30);
x_12 = x_5;
x_13 = x_38;
goto block_17;
}
}
block_96:
{
lean_object* x_39; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_39 = lean_infer_type(x_30, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Expr_getAppFn(x_40);
switch (lean_obj_tag(x_42)) {
case 0:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_3);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec(x_42);
x_44 = l_Lean_Expr_bvar___override(x_43);
x_45 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2_spec__2___redArg___lam__0(x_40, x_5, x_44, x_7, x_8, x_9, x_10, x_41);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_44);
lean_dec(x_5);
x_18 = x_45;
goto block_23;
}
case 1:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_3);
x_46 = lean_ctor_get(x_42, 0);
lean_inc(x_46);
lean_dec(x_42);
x_47 = l_Lean_Expr_fvar___override(x_46);
x_48 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2_spec__2___redArg___lam__0(x_40, x_5, x_47, x_7, x_8, x_9, x_10, x_41);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_47);
lean_dec(x_5);
x_18 = x_48;
goto block_23;
}
case 2:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_3);
x_49 = lean_ctor_get(x_42, 0);
lean_inc(x_49);
lean_dec(x_42);
x_50 = l_Lean_Expr_mvar___override(x_49);
x_51 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2_spec__2___redArg___lam__0(x_40, x_5, x_50, x_7, x_8, x_9, x_10, x_41);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_50);
lean_dec(x_5);
x_18 = x_51;
goto block_23;
}
case 3:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_3);
x_52 = lean_ctor_get(x_42, 0);
lean_inc(x_52);
lean_dec(x_42);
x_53 = l_Lean_Expr_sort___override(x_52);
x_54 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2_spec__2___redArg___lam__0(x_40, x_5, x_53, x_7, x_8, x_9, x_10, x_41);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_53);
lean_dec(x_5);
x_18 = x_54;
goto block_23;
}
case 4:
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_40);
x_55 = lean_ctor_get(x_42, 0);
lean_inc(x_55);
lean_dec(x_42);
x_56 = lean_array_push(x_5, x_55);
x_12 = x_56;
x_13 = x_41;
goto block_17;
}
case 5:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_3);
x_57 = lean_ctor_get(x_42, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_42, 1);
lean_inc(x_58);
lean_dec(x_42);
x_59 = l_Lean_Expr_app___override(x_57, x_58);
x_60 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2_spec__2___redArg___lam__0(x_40, x_5, x_59, x_7, x_8, x_9, x_10, x_41);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_59);
lean_dec(x_5);
x_18 = x_60;
goto block_23;
}
case 6:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_3);
x_61 = lean_ctor_get(x_42, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_42, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_42, 2);
lean_inc(x_63);
x_64 = lean_ctor_get_uint8(x_42, sizeof(void*)*3 + 8);
lean_dec(x_42);
x_65 = l_Lean_Expr_lam___override(x_61, x_62, x_63, x_64);
x_66 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2_spec__2___redArg___lam__0(x_40, x_5, x_65, x_7, x_8, x_9, x_10, x_41);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_65);
lean_dec(x_5);
x_18 = x_66;
goto block_23;
}
case 7:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_3);
x_67 = lean_ctor_get(x_42, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_42, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_42, 2);
lean_inc(x_69);
x_70 = lean_ctor_get_uint8(x_42, sizeof(void*)*3 + 8);
lean_dec(x_42);
x_71 = l_Lean_Expr_forallE___override(x_67, x_68, x_69, x_70);
x_72 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2_spec__2___redArg___lam__0(x_40, x_5, x_71, x_7, x_8, x_9, x_10, x_41);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_71);
lean_dec(x_5);
x_18 = x_72;
goto block_23;
}
case 8:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_3);
x_73 = lean_ctor_get(x_42, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_42, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_42, 2);
lean_inc(x_75);
x_76 = lean_ctor_get(x_42, 3);
lean_inc(x_76);
x_77 = lean_ctor_get_uint8(x_42, sizeof(void*)*4 + 8);
lean_dec(x_42);
x_78 = l_Lean_Expr_letE___override(x_73, x_74, x_75, x_76, x_77);
x_79 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2_spec__2___redArg___lam__0(x_40, x_5, x_78, x_7, x_8, x_9, x_10, x_41);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_78);
lean_dec(x_5);
x_18 = x_79;
goto block_23;
}
case 9:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_3);
x_80 = lean_ctor_get(x_42, 0);
lean_inc(x_80);
lean_dec(x_42);
x_81 = l_Lean_Expr_lit___override(x_80);
x_82 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2_spec__2___redArg___lam__0(x_40, x_5, x_81, x_7, x_8, x_9, x_10, x_41);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_81);
lean_dec(x_5);
x_18 = x_82;
goto block_23;
}
case 10:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_3);
x_83 = lean_ctor_get(x_42, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_42, 1);
lean_inc(x_84);
lean_dec(x_42);
x_85 = l_Lean_Expr_mdata___override(x_83, x_84);
x_86 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2_spec__2___redArg___lam__0(x_40, x_5, x_85, x_7, x_8, x_9, x_10, x_41);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_85);
lean_dec(x_5);
x_18 = x_86;
goto block_23;
}
default: 
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_3);
x_87 = lean_ctor_get(x_42, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_42, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_42, 2);
lean_inc(x_89);
lean_dec(x_42);
x_90 = l_Lean_Expr_proj___override(x_87, x_88, x_89);
x_91 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2_spec__2___redArg___lam__0(x_40, x_5, x_90, x_7, x_8, x_9, x_10, x_41);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_90);
lean_dec(x_5);
x_18 = x_91;
goto block_23;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_92 = !lean_is_exclusive(x_39);
if (x_92 == 0)
{
return x_39;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_39, 0);
x_94 = lean_ctor_get(x_39, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_39);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_30);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_100 = !lean_is_exclusive(x_36);
if (x_100 == 0)
{
return x_36;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_36, 0);
x_102 = lean_ctor_get(x_36, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_36);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
block_17:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_4, 2);
x_15 = lean_nat_add(x_6, x_14);
x_16 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_12, x_15, x_7, x_8, x_9, x_10, x_13);
return x_16;
}
block_23:
{
uint8_t x_19; 
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCustomEliminator___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_mk_empty_array_with_capacity(x_11);
x_13 = lean_ctor_get(x_1, 3);
x_14 = lean_array_get_size(x_13);
x_15 = lean_unsigned_to_nat(1u);
lean_inc(x_14);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
x_17 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2___redArg(x_13, x_4, x_14, x_16, x_12, x_11, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
lean_ctor_set_uint8(x_20, sizeof(void*)*2, x_2);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_3);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_2);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCustomEliminator(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_9 = l_Lean_Meta_getElimInfo(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_1);
x_12 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_1, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(x_2);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_mkCustomEliminator___lam__0___boxed), 10, 3);
lean_closure_set(x_16, 0, x_10);
lean_closure_set(x_16, 1, x_15);
lean_closure_set(x_16, 2, x_1);
x_17 = l_Lean_ConstantInfo_type(x_13);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_unbox(x_18);
x_20 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1(lean_box(0), x_17, x_16, x_19, x_3, x_4, x_5, x_6, x_14);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_12);
if (x_21 == 0)
{
return x_12;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_12, 0);
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_12);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_9);
if (x_25 == 0)
{
return x_9;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_exprDependsOn___at___Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_exprDependsOn___at___Lean_Meta_mkCustomEliminator_spec__0___redArg___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___Lean_Meta_mkCustomEliminator_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_exprDependsOn___at___Lean_Meta_mkCustomEliminator_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___Lean_Meta_mkCustomEliminator_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_exprDependsOn___at___Lean_Meta_mkCustomEliminator_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2_spec__2___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_mkCustomEliminator_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCustomEliminator___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_Meta_mkCustomEliminator___lam__0(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCustomEliminator___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_mkCustomEliminator(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addCustomEliminator_spec__0___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_take(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_5, 6);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
x_14 = l_Lean_ScopedEnvExtension_addCore___redArg(x_13, x_1, x_2, x_3, x_12);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_10, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_10, 3);
lean_inc(x_17);
x_18 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_18);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_19);
lean_ctor_set(x_8, 1, x_19);
lean_ctor_set(x_8, 0, x_19);
x_20 = lean_ctor_get(x_10, 5);
lean_inc(x_20);
x_21 = lean_ctor_get(x_10, 6);
lean_inc(x_21);
x_22 = lean_ctor_get(x_10, 7);
lean_inc(x_22);
lean_dec(x_10);
x_23 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_15);
lean_ctor_set(x_23, 2, x_16);
lean_ctor_set(x_23, 3, x_17);
lean_ctor_set(x_23, 4, x_8);
lean_ctor_set(x_23, 5, x_20);
lean_ctor_set(x_23, 6, x_21);
lean_ctor_set(x_23, 7, x_22);
x_24 = lean_st_ref_set(x_6, x_23, x_11);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_st_ref_take(x_4, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_inc(x_18);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_18);
lean_inc(x_18);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_18);
lean_inc(x_18);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_18);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_18);
lean_inc(x_33);
lean_inc(x_30);
x_34 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_31);
lean_ctor_set(x_34, 2, x_32);
lean_ctor_set(x_34, 3, x_30);
lean_ctor_set(x_34, 4, x_33);
lean_ctor_set(x_34, 5, x_33);
x_35 = lean_ctor_get(x_27, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_27, 3);
lean_inc(x_36);
x_37 = lean_ctor_get(x_27, 4);
lean_inc(x_37);
lean_dec(x_27);
x_38 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_38, 0, x_29);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 4, x_37);
x_39 = lean_st_ref_set(x_4, x_38, x_28);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
x_42 = lean_box(0);
lean_ctor_set(x_39, 0, x_42);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_46 = lean_ctor_get(x_8, 0);
x_47 = lean_ctor_get(x_8, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_8);
x_48 = lean_ctor_get(x_5, 6);
lean_inc(x_48);
lean_dec(x_5);
x_49 = lean_ctor_get(x_46, 0);
lean_inc(x_49);
x_50 = l_Lean_ScopedEnvExtension_addCore___redArg(x_49, x_1, x_2, x_3, x_48);
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_46, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_46, 3);
lean_inc(x_53);
x_54 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_54);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
lean_inc(x_55);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_ctor_get(x_46, 5);
lean_inc(x_57);
x_58 = lean_ctor_get(x_46, 6);
lean_inc(x_58);
x_59 = lean_ctor_get(x_46, 7);
lean_inc(x_59);
lean_dec(x_46);
x_60 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_60, 0, x_50);
lean_ctor_set(x_60, 1, x_51);
lean_ctor_set(x_60, 2, x_52);
lean_ctor_set(x_60, 3, x_53);
lean_ctor_set(x_60, 4, x_56);
lean_ctor_set(x_60, 5, x_57);
lean_ctor_set(x_60, 6, x_58);
lean_ctor_set(x_60, 7, x_59);
x_61 = lean_st_ref_set(x_6, x_60, x_47);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_st_ref_take(x_4, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
lean_inc(x_54);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_54);
lean_inc(x_54);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_54);
lean_inc(x_54);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_54);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_54);
lean_inc(x_70);
lean_inc(x_67);
x_71 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_71, 0, x_67);
lean_ctor_set(x_71, 1, x_68);
lean_ctor_set(x_71, 2, x_69);
lean_ctor_set(x_71, 3, x_67);
lean_ctor_set(x_71, 4, x_70);
lean_ctor_set(x_71, 5, x_70);
x_72 = lean_ctor_get(x_64, 2);
lean_inc(x_72);
x_73 = lean_ctor_get(x_64, 3);
lean_inc(x_73);
x_74 = lean_ctor_get(x_64, 4);
lean_inc(x_74);
lean_dec(x_64);
x_75 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_75, 0, x_66);
lean_ctor_set(x_75, 1, x_71);
lean_ctor_set(x_75, 2, x_72);
lean_ctor_set(x_75, 3, x_73);
lean_ctor_set(x_75, 4, x_74);
x_76 = lean_st_ref_set(x_4, x_75, x_65);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_78 = x_76;
} else {
 lean_dec_ref(x_76);
 x_78 = lean_box(0);
}
x_79 = lean_box(0);
if (lean_is_scalar(x_78)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_78;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_77);
return x_80;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addCustomEliminator_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addCustomEliminator_spec__0___redArg(x_4, x_5, x_6, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addCustomEliminator(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_9 = l_Lean_Meta_mkCustomEliminator(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_customEliminatorExt;
x_13 = l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addCustomEliminator_spec__0___redArg(x_12, x_10, x_2, x_5, x_6, x_7, x_11);
lean_dec(x_7);
lean_dec(x_5);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addCustomEliminator_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addCustomEliminator_spec__0___redArg(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addCustomEliminator_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_6);
lean_dec(x_6);
x_13 = l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addCustomEliminator_spec__0(x_1, x_2, x_3, x_4, x_5, x_12, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addCustomEliminator___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Meta_addCustomEliminator(x_1, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Tactic_ElimInfo___hyg_3180_(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint64_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; lean_object* x_75; 
x_7 = lean_box(0);
x_8 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_unsigned_to_nat(5u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_nat_pow(x_9, x_12);
lean_dec(x_12);
x_14 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_15 = lean_usize_to_nat(x_14);
x_16 = lean_mk_empty_array_with_capacity(x_15);
lean_dec(x_15);
lean_inc(x_16);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_8);
lean_inc(x_8);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_8);
lean_inc(x_8);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_8);
lean_inc(x_8);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_8);
lean_inc(x_8);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_8);
lean_inc(x_8);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_8);
lean_inc(x_19);
x_25 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_18);
lean_ctor_set(x_25, 2, x_18);
lean_ctor_set(x_25, 3, x_19);
lean_ctor_set(x_25, 4, x_20);
lean_ctor_set(x_25, 5, x_21);
lean_ctor_set(x_25, 6, x_22);
lean_ctor_set(x_25, 7, x_23);
lean_ctor_set(x_25, 8, x_24);
lean_inc(x_8);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_8);
lean_inc(x_8);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_8);
lean_inc(x_8);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_8);
lean_inc(x_8);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_8);
lean_inc(x_29);
lean_inc(x_26);
x_30 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_27);
lean_ctor_set(x_30, 2, x_28);
lean_ctor_set(x_30, 3, x_26);
lean_ctor_set(x_30, 4, x_29);
lean_ctor_set(x_30, 5, x_29);
lean_inc(x_16);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_16);
lean_inc(x_16);
x_32 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_16);
lean_ctor_set(x_32, 2, x_18);
lean_ctor_set(x_32, 3, x_18);
lean_ctor_set_usize(x_32, 4, x_11);
lean_inc(x_8);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_8);
lean_inc_n(x_19, 2);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_19);
lean_ctor_set(x_34, 1, x_19);
lean_ctor_set(x_34, 2, x_19);
lean_ctor_set(x_34, 3, x_33);
x_35 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_35, 0, x_25);
lean_ctor_set(x_35, 1, x_30);
lean_ctor_set(x_35, 2, x_7);
lean_ctor_set(x_35, 3, x_32);
lean_ctor_set(x_35, 4, x_34);
x_36 = lean_st_mk_ref(x_35, x_6);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_box(1);
x_40 = lean_box(0);
x_41 = lean_box(2);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_8);
x_43 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_43, 0, x_17);
lean_ctor_set(x_43, 1, x_16);
lean_ctor_set(x_43, 2, x_18);
lean_ctor_set(x_43, 3, x_18);
lean_ctor_set_usize(x_43, 4, x_11);
x_44 = lean_box(1);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 0, 18);
x_47 = lean_unbox(x_45);
lean_ctor_set_uint8(x_46, 0, x_47);
x_48 = lean_unbox(x_45);
lean_ctor_set_uint8(x_46, 1, x_48);
x_49 = lean_unbox(x_45);
lean_ctor_set_uint8(x_46, 2, x_49);
x_50 = lean_unbox(x_45);
lean_ctor_set_uint8(x_46, 3, x_50);
x_51 = lean_unbox(x_45);
lean_ctor_set_uint8(x_46, 4, x_51);
x_52 = lean_unbox(x_44);
lean_ctor_set_uint8(x_46, 5, x_52);
x_53 = lean_unbox(x_44);
lean_ctor_set_uint8(x_46, 6, x_53);
x_54 = lean_unbox(x_45);
lean_ctor_set_uint8(x_46, 7, x_54);
x_55 = lean_unbox(x_44);
lean_ctor_set_uint8(x_46, 8, x_55);
x_56 = lean_unbox(x_39);
lean_ctor_set_uint8(x_46, 9, x_56);
x_57 = lean_unbox(x_40);
lean_ctor_set_uint8(x_46, 10, x_57);
x_58 = lean_unbox(x_44);
lean_ctor_set_uint8(x_46, 11, x_58);
x_59 = lean_unbox(x_44);
lean_ctor_set_uint8(x_46, 12, x_59);
x_60 = lean_unbox(x_44);
lean_ctor_set_uint8(x_46, 13, x_60);
x_61 = lean_unbox(x_41);
lean_ctor_set_uint8(x_46, 14, x_61);
x_62 = lean_unbox(x_44);
lean_ctor_set_uint8(x_46, 15, x_62);
x_63 = lean_unbox(x_44);
lean_ctor_set_uint8(x_46, 16, x_63);
x_64 = lean_unbox(x_44);
lean_ctor_set_uint8(x_46, 17, x_64);
x_65 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_46);
x_66 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_66, 0, x_42);
lean_ctor_set(x_66, 1, x_43);
lean_ctor_set(x_66, 2, x_7);
x_67 = lean_mk_empty_array_with_capacity(x_18);
x_68 = lean_box(0);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_70, 0, x_46);
lean_ctor_set(x_70, 1, x_7);
lean_ctor_set(x_70, 2, x_66);
lean_ctor_set(x_70, 3, x_67);
lean_ctor_set(x_70, 4, x_68);
lean_ctor_set(x_70, 5, x_18);
lean_ctor_set(x_70, 6, x_69);
lean_ctor_set_uint64(x_70, sizeof(void*)*7, x_65);
x_71 = lean_unbox(x_45);
lean_ctor_set_uint8(x_70, sizeof(void*)*7 + 8, x_71);
x_72 = lean_unbox(x_45);
lean_ctor_set_uint8(x_70, sizeof(void*)*7 + 9, x_72);
x_73 = lean_unbox(x_45);
lean_ctor_set_uint8(x_70, sizeof(void*)*7 + 10, x_73);
x_74 = lean_unbox(x_44);
lean_inc(x_37);
x_75 = l_Lean_Meta_addCustomEliminator(x_1, x_3, x_74, x_70, x_37, x_4, x_5, x_38);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_st_ref_get(x_37, x_76);
lean_dec(x_37);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_77, 0);
lean_dec(x_79);
x_80 = lean_box(0);
lean_ctor_set(x_77, 0, x_80);
return x_77;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_77, 1);
lean_inc(x_81);
lean_dec(x_77);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
else
{
lean_dec(x_37);
return x_75;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__1____x40_Lean_Meta_Tactic_ElimInfo___hyg_3180_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_mk_string_unchecked("attribute cannot be erased", 26, 26);
x_6 = l_Lean_stringToMessageData(x_5);
lean_dec(x_5);
x_7 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_ElimInfo___hyg_3180_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Tactic_ElimInfo___hyg_3180____boxed), 6, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_initFn___lam__1____x40_Lean_Meta_Tactic_ElimInfo___hyg_3180____boxed), 4, 0);
x_4 = lean_box(0);
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_5);
x_6 = l_Lean_Name_str___override(x_4, x_5);
x_7 = lean_mk_string_unchecked("Meta", 4, 4);
lean_inc(x_7);
x_8 = l_Lean_Name_str___override(x_6, x_7);
x_9 = lean_mk_string_unchecked("initFn", 6, 6);
x_10 = l_Lean_Name_str___override(x_8, x_9);
x_11 = lean_mk_string_unchecked("_@", 2, 2);
x_12 = l_Lean_Name_str___override(x_10, x_11);
x_13 = l_Lean_Name_str___override(x_12, x_5);
x_14 = l_Lean_Name_str___override(x_13, x_7);
x_15 = lean_mk_string_unchecked("Tactic", 6, 6);
x_16 = l_Lean_Name_str___override(x_14, x_15);
x_17 = lean_mk_string_unchecked("ElimInfo", 8, 8);
x_18 = l_Lean_Name_str___override(x_16, x_17);
x_19 = lean_mk_string_unchecked("_hyg", 4, 4);
x_20 = l_Lean_Name_str___override(x_18, x_19);
x_21 = lean_unsigned_to_nat(3180u);
x_22 = l_Lean_Name_num___override(x_20, x_21);
x_23 = lean_mk_string_unchecked("induction_eliminator", 20, 20);
x_24 = l_Lean_Name_mkStr1(x_23);
x_25 = lean_mk_string_unchecked("custom `rec`-like eliminator for the `induction` tactic", 55, 55);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_25);
x_28 = lean_unbox(x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*3, x_28);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_2);
lean_ctor_set(x_29, 2, x_3);
x_30 = l_Lean_registerBuiltinAttribute(x_29, x_1);
return x_30;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Tactic_ElimInfo___hyg_3180____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Tactic_ElimInfo___hyg_3180_(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__1____x40_Lean_Meta_Tactic_ElimInfo___hyg_3180____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_initFn___lam__1____x40_Lean_Meta_Tactic_ElimInfo___hyg_3180_(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Tactic_ElimInfo___hyg_3258_(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint64_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; lean_object* x_75; 
x_7 = lean_box(0);
x_8 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_unsigned_to_nat(5u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_nat_pow(x_9, x_12);
lean_dec(x_12);
x_14 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_15 = lean_usize_to_nat(x_14);
x_16 = lean_mk_empty_array_with_capacity(x_15);
lean_dec(x_15);
lean_inc(x_16);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_8);
lean_inc(x_8);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_8);
lean_inc(x_8);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_8);
lean_inc(x_8);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_8);
lean_inc(x_8);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_8);
lean_inc(x_8);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_8);
lean_inc(x_19);
x_25 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_18);
lean_ctor_set(x_25, 2, x_18);
lean_ctor_set(x_25, 3, x_19);
lean_ctor_set(x_25, 4, x_20);
lean_ctor_set(x_25, 5, x_21);
lean_ctor_set(x_25, 6, x_22);
lean_ctor_set(x_25, 7, x_23);
lean_ctor_set(x_25, 8, x_24);
lean_inc(x_8);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_8);
lean_inc(x_8);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_8);
lean_inc(x_8);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_8);
lean_inc(x_8);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_8);
lean_inc(x_29);
lean_inc(x_26);
x_30 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_27);
lean_ctor_set(x_30, 2, x_28);
lean_ctor_set(x_30, 3, x_26);
lean_ctor_set(x_30, 4, x_29);
lean_ctor_set(x_30, 5, x_29);
lean_inc(x_16);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_16);
lean_inc(x_16);
x_32 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_16);
lean_ctor_set(x_32, 2, x_18);
lean_ctor_set(x_32, 3, x_18);
lean_ctor_set_usize(x_32, 4, x_11);
lean_inc(x_8);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_8);
lean_inc_n(x_19, 2);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_19);
lean_ctor_set(x_34, 1, x_19);
lean_ctor_set(x_34, 2, x_19);
lean_ctor_set(x_34, 3, x_33);
x_35 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_35, 0, x_25);
lean_ctor_set(x_35, 1, x_30);
lean_ctor_set(x_35, 2, x_7);
lean_ctor_set(x_35, 3, x_32);
lean_ctor_set(x_35, 4, x_34);
x_36 = lean_st_mk_ref(x_35, x_6);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_box(1);
x_40 = lean_box(1);
x_41 = lean_box(0);
x_42 = lean_box(2);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_8);
x_44 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_44, 0, x_17);
lean_ctor_set(x_44, 1, x_16);
lean_ctor_set(x_44, 2, x_18);
lean_ctor_set(x_44, 3, x_18);
lean_ctor_set_usize(x_44, 4, x_11);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 0, 18);
x_47 = lean_unbox(x_45);
lean_ctor_set_uint8(x_46, 0, x_47);
x_48 = lean_unbox(x_45);
lean_ctor_set_uint8(x_46, 1, x_48);
x_49 = lean_unbox(x_45);
lean_ctor_set_uint8(x_46, 2, x_49);
x_50 = lean_unbox(x_45);
lean_ctor_set_uint8(x_46, 3, x_50);
x_51 = lean_unbox(x_45);
lean_ctor_set_uint8(x_46, 4, x_51);
x_52 = lean_unbox(x_39);
lean_ctor_set_uint8(x_46, 5, x_52);
x_53 = lean_unbox(x_39);
lean_ctor_set_uint8(x_46, 6, x_53);
x_54 = lean_unbox(x_45);
lean_ctor_set_uint8(x_46, 7, x_54);
x_55 = lean_unbox(x_39);
lean_ctor_set_uint8(x_46, 8, x_55);
x_56 = lean_unbox(x_40);
lean_ctor_set_uint8(x_46, 9, x_56);
x_57 = lean_unbox(x_41);
lean_ctor_set_uint8(x_46, 10, x_57);
x_58 = lean_unbox(x_39);
lean_ctor_set_uint8(x_46, 11, x_58);
x_59 = lean_unbox(x_39);
lean_ctor_set_uint8(x_46, 12, x_59);
x_60 = lean_unbox(x_39);
lean_ctor_set_uint8(x_46, 13, x_60);
x_61 = lean_unbox(x_42);
lean_ctor_set_uint8(x_46, 14, x_61);
x_62 = lean_unbox(x_39);
lean_ctor_set_uint8(x_46, 15, x_62);
x_63 = lean_unbox(x_39);
lean_ctor_set_uint8(x_46, 16, x_63);
x_64 = lean_unbox(x_39);
lean_ctor_set_uint8(x_46, 17, x_64);
x_65 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_46);
x_66 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_66, 0, x_43);
lean_ctor_set(x_66, 1, x_44);
lean_ctor_set(x_66, 2, x_7);
x_67 = lean_mk_empty_array_with_capacity(x_18);
x_68 = lean_box(0);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_70, 0, x_46);
lean_ctor_set(x_70, 1, x_7);
lean_ctor_set(x_70, 2, x_66);
lean_ctor_set(x_70, 3, x_67);
lean_ctor_set(x_70, 4, x_68);
lean_ctor_set(x_70, 5, x_18);
lean_ctor_set(x_70, 6, x_69);
lean_ctor_set_uint64(x_70, sizeof(void*)*7, x_65);
x_71 = lean_unbox(x_45);
lean_ctor_set_uint8(x_70, sizeof(void*)*7 + 8, x_71);
x_72 = lean_unbox(x_45);
lean_ctor_set_uint8(x_70, sizeof(void*)*7 + 9, x_72);
x_73 = lean_unbox(x_45);
lean_ctor_set_uint8(x_70, sizeof(void*)*7 + 10, x_73);
x_74 = lean_unbox(x_45);
lean_inc(x_37);
x_75 = l_Lean_Meta_addCustomEliminator(x_1, x_3, x_74, x_70, x_37, x_4, x_5, x_38);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_st_ref_get(x_37, x_76);
lean_dec(x_37);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_77, 0);
lean_dec(x_79);
x_80 = lean_box(0);
lean_ctor_set(x_77, 0, x_80);
return x_77;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_77, 1);
lean_inc(x_81);
lean_dec(x_77);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
else
{
lean_dec(x_37);
return x_75;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_ElimInfo___hyg_3258_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Tactic_ElimInfo___hyg_3258____boxed), 6, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_initFn___lam__1____x40_Lean_Meta_Tactic_ElimInfo___hyg_3180____boxed), 4, 0);
x_4 = lean_box(0);
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_5);
x_6 = l_Lean_Name_str___override(x_4, x_5);
x_7 = lean_mk_string_unchecked("Meta", 4, 4);
lean_inc(x_7);
x_8 = l_Lean_Name_str___override(x_6, x_7);
x_9 = lean_mk_string_unchecked("initFn", 6, 6);
x_10 = l_Lean_Name_str___override(x_8, x_9);
x_11 = lean_mk_string_unchecked("_@", 2, 2);
x_12 = l_Lean_Name_str___override(x_10, x_11);
x_13 = l_Lean_Name_str___override(x_12, x_5);
x_14 = l_Lean_Name_str___override(x_13, x_7);
x_15 = lean_mk_string_unchecked("Tactic", 6, 6);
x_16 = l_Lean_Name_str___override(x_14, x_15);
x_17 = lean_mk_string_unchecked("ElimInfo", 8, 8);
x_18 = l_Lean_Name_str___override(x_16, x_17);
x_19 = lean_mk_string_unchecked("_hyg", 4, 4);
x_20 = l_Lean_Name_str___override(x_18, x_19);
x_21 = lean_unsigned_to_nat(3258u);
x_22 = l_Lean_Name_num___override(x_20, x_21);
x_23 = lean_mk_string_unchecked("cases_eliminator", 16, 16);
x_24 = l_Lean_Name_mkStr1(x_23);
x_25 = lean_mk_string_unchecked("custom `casesOn`-like eliminator for the `cases` tactic", 55, 55);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_25);
x_28 = lean_unbox(x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*3, x_28);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_2);
lean_ctor_set(x_29, 2, x_3);
x_30 = l_Lean_registerBuiltinAttribute(x_29, x_1);
return x_30;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Tactic_ElimInfo___hyg_3258____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Tactic_ElimInfo___hyg_3258_(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminators___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lean_Meta_instInhabitedCustomEliminators;
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Meta_customEliminatorExt;
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
lean_dec(x_10);
x_12 = l_Lean_ScopedEnvExtension_getState___redArg(x_6, x_8, x_7, x_11);
lean_ctor_set(x_3, 0, x_12);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_15 = l_Lean_Meta_instInhabitedCustomEliminators;
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Lean_Meta_customEliminatorExt;
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get_uint8(x_19, sizeof(void*)*3);
lean_dec(x_19);
x_21 = l_Lean_ScopedEnvExtension_getState___redArg(x_15, x_17, x_16, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_14);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminators(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_getCustomEliminators___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminators___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_getCustomEliminators___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminators___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_getCustomEliminators(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getCustomEliminator_x3f_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_1);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getCustomEliminator_x3f_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_17; uint8_t x_26; 
x_26 = lean_usize_dec_lt(x_3, x_2);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_4);
lean_ctor_set(x_27, 1, x_9);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_array_uget(x_1, x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_29 = lean_infer_type(x_28, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_30, x_6, x_31);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
x_36 = lean_ctor_get(x_4, 1);
lean_inc(x_36);
lean_dec(x_4);
x_37 = l_Lean_Expr_headBeta(x_34);
x_38 = l_Lean_Expr_getAppFn(x_37);
lean_dec(x_37);
switch (lean_obj_tag(x_38)) {
case 0:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_free_object(x_32);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l_Lean_Expr_bvar___override(x_39);
x_41 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getCustomEliminator_x3f_spec__0___lam__0(x_36, x_40, x_5, x_6, x_7, x_8, x_35);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_40);
x_17 = x_41;
goto block_25;
}
case 1:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_free_object(x_32);
x_42 = lean_ctor_get(x_38, 0);
lean_inc(x_42);
lean_dec(x_38);
x_43 = l_Lean_Expr_fvar___override(x_42);
x_44 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getCustomEliminator_x3f_spec__0___lam__0(x_36, x_43, x_5, x_6, x_7, x_8, x_35);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_43);
x_17 = x_44;
goto block_25;
}
case 2:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_free_object(x_32);
x_45 = lean_ctor_get(x_38, 0);
lean_inc(x_45);
lean_dec(x_38);
x_46 = l_Lean_Expr_mvar___override(x_45);
x_47 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getCustomEliminator_x3f_spec__0___lam__0(x_36, x_46, x_5, x_6, x_7, x_8, x_35);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_46);
x_17 = x_47;
goto block_25;
}
case 3:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_free_object(x_32);
x_48 = lean_ctor_get(x_38, 0);
lean_inc(x_48);
lean_dec(x_38);
x_49 = l_Lean_Expr_sort___override(x_48);
x_50 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getCustomEliminator_x3f_spec__0___lam__0(x_36, x_49, x_5, x_6, x_7, x_8, x_35);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_49);
x_17 = x_50;
goto block_25;
}
case 4:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_38, 0);
lean_inc(x_51);
lean_dec(x_38);
x_52 = lean_box(0);
x_53 = lean_array_push(x_36, x_51);
lean_ctor_set(x_32, 1, x_53);
lean_ctor_set(x_32, 0, x_52);
x_10 = x_32;
x_11 = x_35;
goto block_16;
}
case 5:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_free_object(x_32);
x_54 = lean_ctor_get(x_38, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_38, 1);
lean_inc(x_55);
lean_dec(x_38);
x_56 = l_Lean_Expr_app___override(x_54, x_55);
x_57 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getCustomEliminator_x3f_spec__0___lam__0(x_36, x_56, x_5, x_6, x_7, x_8, x_35);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_56);
x_17 = x_57;
goto block_25;
}
case 6:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; 
lean_free_object(x_32);
x_58 = lean_ctor_get(x_38, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_38, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_38, 2);
lean_inc(x_60);
x_61 = lean_ctor_get_uint8(x_38, sizeof(void*)*3 + 8);
lean_dec(x_38);
x_62 = l_Lean_Expr_lam___override(x_58, x_59, x_60, x_61);
x_63 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getCustomEliminator_x3f_spec__0___lam__0(x_36, x_62, x_5, x_6, x_7, x_8, x_35);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_62);
x_17 = x_63;
goto block_25;
}
case 7:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; 
lean_free_object(x_32);
x_64 = lean_ctor_get(x_38, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_38, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_38, 2);
lean_inc(x_66);
x_67 = lean_ctor_get_uint8(x_38, sizeof(void*)*3 + 8);
lean_dec(x_38);
x_68 = l_Lean_Expr_forallE___override(x_64, x_65, x_66, x_67);
x_69 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getCustomEliminator_x3f_spec__0___lam__0(x_36, x_68, x_5, x_6, x_7, x_8, x_35);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_68);
x_17 = x_69;
goto block_25;
}
case 8:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; 
lean_free_object(x_32);
x_70 = lean_ctor_get(x_38, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_38, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_38, 2);
lean_inc(x_72);
x_73 = lean_ctor_get(x_38, 3);
lean_inc(x_73);
x_74 = lean_ctor_get_uint8(x_38, sizeof(void*)*4 + 8);
lean_dec(x_38);
x_75 = l_Lean_Expr_letE___override(x_70, x_71, x_72, x_73, x_74);
x_76 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getCustomEliminator_x3f_spec__0___lam__0(x_36, x_75, x_5, x_6, x_7, x_8, x_35);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_75);
x_17 = x_76;
goto block_25;
}
case 9:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_free_object(x_32);
x_77 = lean_ctor_get(x_38, 0);
lean_inc(x_77);
lean_dec(x_38);
x_78 = l_Lean_Expr_lit___override(x_77);
x_79 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getCustomEliminator_x3f_spec__0___lam__0(x_36, x_78, x_5, x_6, x_7, x_8, x_35);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_78);
x_17 = x_79;
goto block_25;
}
case 10:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_free_object(x_32);
x_80 = lean_ctor_get(x_38, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_38, 1);
lean_inc(x_81);
lean_dec(x_38);
x_82 = l_Lean_Expr_mdata___override(x_80, x_81);
x_83 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getCustomEliminator_x3f_spec__0___lam__0(x_36, x_82, x_5, x_6, x_7, x_8, x_35);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_82);
x_17 = x_83;
goto block_25;
}
default: 
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_free_object(x_32);
x_84 = lean_ctor_get(x_38, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_38, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_38, 2);
lean_inc(x_86);
lean_dec(x_38);
x_87 = l_Lean_Expr_proj___override(x_84, x_85, x_86);
x_88 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getCustomEliminator_x3f_spec__0___lam__0(x_36, x_87, x_5, x_6, x_7, x_8, x_35);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_87);
x_17 = x_88;
goto block_25;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_ctor_get(x_32, 0);
x_90 = lean_ctor_get(x_32, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_32);
x_91 = lean_ctor_get(x_4, 1);
lean_inc(x_91);
lean_dec(x_4);
x_92 = l_Lean_Expr_headBeta(x_89);
x_93 = l_Lean_Expr_getAppFn(x_92);
lean_dec(x_92);
switch (lean_obj_tag(x_93)) {
case 0:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
lean_dec(x_93);
x_95 = l_Lean_Expr_bvar___override(x_94);
x_96 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getCustomEliminator_x3f_spec__0___lam__0(x_91, x_95, x_5, x_6, x_7, x_8, x_90);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_95);
x_17 = x_96;
goto block_25;
}
case 1:
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_93, 0);
lean_inc(x_97);
lean_dec(x_93);
x_98 = l_Lean_Expr_fvar___override(x_97);
x_99 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getCustomEliminator_x3f_spec__0___lam__0(x_91, x_98, x_5, x_6, x_7, x_8, x_90);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_98);
x_17 = x_99;
goto block_25;
}
case 2:
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_93, 0);
lean_inc(x_100);
lean_dec(x_93);
x_101 = l_Lean_Expr_mvar___override(x_100);
x_102 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getCustomEliminator_x3f_spec__0___lam__0(x_91, x_101, x_5, x_6, x_7, x_8, x_90);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_101);
x_17 = x_102;
goto block_25;
}
case 3:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_93, 0);
lean_inc(x_103);
lean_dec(x_93);
x_104 = l_Lean_Expr_sort___override(x_103);
x_105 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getCustomEliminator_x3f_spec__0___lam__0(x_91, x_104, x_5, x_6, x_7, x_8, x_90);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_104);
x_17 = x_105;
goto block_25;
}
case 4:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = lean_ctor_get(x_93, 0);
lean_inc(x_106);
lean_dec(x_93);
x_107 = lean_box(0);
x_108 = lean_array_push(x_91, x_106);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
x_10 = x_109;
x_11 = x_90;
goto block_16;
}
case 5:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_93, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_93, 1);
lean_inc(x_111);
lean_dec(x_93);
x_112 = l_Lean_Expr_app___override(x_110, x_111);
x_113 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getCustomEliminator_x3f_spec__0___lam__0(x_91, x_112, x_5, x_6, x_7, x_8, x_90);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_112);
x_17 = x_113;
goto block_25;
}
case 6:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; 
x_114 = lean_ctor_get(x_93, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_93, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_93, 2);
lean_inc(x_116);
x_117 = lean_ctor_get_uint8(x_93, sizeof(void*)*3 + 8);
lean_dec(x_93);
x_118 = l_Lean_Expr_lam___override(x_114, x_115, x_116, x_117);
x_119 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getCustomEliminator_x3f_spec__0___lam__0(x_91, x_118, x_5, x_6, x_7, x_8, x_90);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_118);
x_17 = x_119;
goto block_25;
}
case 7:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; 
x_120 = lean_ctor_get(x_93, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_93, 1);
lean_inc(x_121);
x_122 = lean_ctor_get(x_93, 2);
lean_inc(x_122);
x_123 = lean_ctor_get_uint8(x_93, sizeof(void*)*3 + 8);
lean_dec(x_93);
x_124 = l_Lean_Expr_forallE___override(x_120, x_121, x_122, x_123);
x_125 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getCustomEliminator_x3f_spec__0___lam__0(x_91, x_124, x_5, x_6, x_7, x_8, x_90);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_124);
x_17 = x_125;
goto block_25;
}
case 8:
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; 
x_126 = lean_ctor_get(x_93, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_93, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_93, 2);
lean_inc(x_128);
x_129 = lean_ctor_get(x_93, 3);
lean_inc(x_129);
x_130 = lean_ctor_get_uint8(x_93, sizeof(void*)*4 + 8);
lean_dec(x_93);
x_131 = l_Lean_Expr_letE___override(x_126, x_127, x_128, x_129, x_130);
x_132 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getCustomEliminator_x3f_spec__0___lam__0(x_91, x_131, x_5, x_6, x_7, x_8, x_90);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_131);
x_17 = x_132;
goto block_25;
}
case 9:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_93, 0);
lean_inc(x_133);
lean_dec(x_93);
x_134 = l_Lean_Expr_lit___override(x_133);
x_135 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getCustomEliminator_x3f_spec__0___lam__0(x_91, x_134, x_5, x_6, x_7, x_8, x_90);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_134);
x_17 = x_135;
goto block_25;
}
case 10:
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_136 = lean_ctor_get(x_93, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_93, 1);
lean_inc(x_137);
lean_dec(x_93);
x_138 = l_Lean_Expr_mdata___override(x_136, x_137);
x_139 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getCustomEliminator_x3f_spec__0___lam__0(x_91, x_138, x_5, x_6, x_7, x_8, x_90);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_138);
x_17 = x_139;
goto block_25;
}
default: 
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_140 = lean_ctor_get(x_93, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_93, 1);
lean_inc(x_141);
x_142 = lean_ctor_get(x_93, 2);
lean_inc(x_142);
lean_dec(x_93);
x_143 = l_Lean_Expr_proj___override(x_140, x_141, x_142);
x_144 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getCustomEliminator_x3f_spec__0___lam__0(x_91, x_143, x_5, x_6, x_7, x_8, x_90);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_143);
x_17 = x_144;
goto block_25;
}
}
}
}
else
{
uint8_t x_145; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_145 = !lean_is_exclusive(x_29);
if (x_145 == 0)
{
return x_29;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_29, 0);
x_147 = lean_ctor_get(x_29, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_29);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
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
block_25:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_array_fget(x_2, x_4);
lean_inc(x_1);
lean_inc(x_5);
x_10 = lean_apply_2(x_1, x_5, x_9);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_4 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_1);
x_15 = lean_array_fget(x_3, x_4);
lean_dec(x_4);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__1_spec__1___redArg(x_1, x_3, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = l_Lean_PersistentHashMap_instInhabitedEntry(lean_box(0), lean_box(0), lean_box(0));
x_8 = lean_unsigned_to_nat(5u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_shift_left(x_11, x_9);
x_13 = lean_usize_sub(x_12, x_11);
x_14 = lean_usize_land(x_3, x_13);
x_15 = lean_usize_to_nat(x_14);
x_16 = lean_array_get(x_7, x_6, x_15);
lean_dec(x_15);
lean_dec(x_6);
switch (lean_obj_tag(x_16)) {
case 0:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_apply_2(x_1, x_4, x_17);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_18);
lean_free_object(x_2);
x_21 = lean_box(0);
return x_21;
}
else
{
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_18);
return x_2;
}
}
case 1:
{
lean_object* x_22; size_t x_23; 
lean_free_object(x_2);
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_usize_shift_right(x_3, x_9);
x_2 = x_22;
x_3 = x_23;
goto _start;
}
default: 
{
lean_object* x_25; 
lean_free_object(x_2);
lean_dec(x_4);
lean_dec(x_1);
x_25 = lean_box(0);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; lean_object* x_30; size_t x_31; size_t x_32; size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; 
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
lean_dec(x_2);
x_27 = l_Lean_PersistentHashMap_instInhabitedEntry(lean_box(0), lean_box(0), lean_box(0));
x_28 = lean_unsigned_to_nat(5u);
x_29 = lean_usize_of_nat(x_28);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_usize_of_nat(x_30);
x_32 = lean_usize_shift_left(x_31, x_29);
x_33 = lean_usize_sub(x_32, x_31);
x_34 = lean_usize_land(x_3, x_33);
x_35 = lean_usize_to_nat(x_34);
x_36 = lean_array_get(x_27, x_26, x_35);
lean_dec(x_35);
lean_dec(x_26);
switch (lean_obj_tag(x_36)) {
case 0:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_apply_2(x_1, x_4, x_37);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_38);
x_41 = lean_box(0);
return x_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_38);
return x_42;
}
}
case 1:
{
lean_object* x_43; size_t x_44; 
x_43 = lean_ctor_get(x_36, 0);
lean_inc(x_43);
lean_dec(x_36);
x_44 = lean_usize_shift_right(x_3, x_29);
x_2 = x_43;
x_3 = x_44;
goto _start;
}
default: 
{
lean_object* x_46; 
lean_dec(x_4);
lean_dec(x_1);
x_46 = lean_box(0);
return x_46;
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_2, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_2, 1);
lean_inc(x_48);
lean_dec(x_2);
x_49 = lean_unsigned_to_nat(0u);
x_50 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__1_spec__1___redArg(x_1, x_47, x_48, x_49, x_4);
lean_dec(x_48);
lean_dec(x_47);
return x_50;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__1___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; uint64_t x_5; lean_object* x_10; lean_object* x_11; uint64_t x_12; uint8_t x_23; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
x_23 = lean_unbox(x_10);
lean_dec(x_10);
if (x_23 == 0)
{
lean_object* x_24; uint64_t x_25; 
x_24 = lean_unsigned_to_nat(13u);
x_25 = lean_uint64_of_nat(x_24);
x_12 = x_25;
goto block_22;
}
else
{
lean_object* x_26; uint64_t x_27; 
x_26 = lean_unsigned_to_nat(11u);
x_27 = lean_uint64_of_nat(x_26);
x_12 = x_27;
goto block_22;
}
block_9:
{
uint64_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_uint64_mix_hash(x_4, x_5);
x_7 = lean_uint64_to_usize(x_6);
x_8 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__1___redArg(x_1, x_2, x_7, x_3);
return x_8;
}
block_22:
{
lean_object* x_13; uint64_t x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_unsigned_to_nat(7u);
x_14 = lean_uint64_of_nat(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_get_size(x_11);
x_17 = lean_nat_dec_lt(x_15, x_16);
if (x_17 == 0)
{
lean_dec(x_16);
lean_dec(x_11);
x_4 = x_12;
x_5 = x_14;
goto block_9;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_16, x_16);
if (x_18 == 0)
{
lean_dec(x_16);
lean_dec(x_11);
x_4 = x_12;
x_5 = x_14;
goto block_9;
}
else
{
size_t x_19; size_t x_20; uint64_t x_21; 
x_19 = lean_usize_of_nat(x_15);
x_20 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_21 = l_Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__0(x_11, x_19, x_20, x_14);
lean_dec(x_11);
x_4 = x_12;
x_5 = x_21;
goto block_9;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_8 = lean_apply_2(x_1, x_5, x_2);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_dec(x_6);
x_3 = x_7;
goto _start;
}
else
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_6);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1_spec__4___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
lean_inc(x_3);
lean_inc(x_1);
x_7 = l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1___redArg(x_1, x_6, x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint64_t x_12; uint64_t x_13; uint64_t x_32; uint8_t x_43; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
x_11 = lean_array_get_size(x_8);
x_43 = lean_unbox(x_9);
lean_dec(x_9);
if (x_43 == 0)
{
lean_object* x_44; uint64_t x_45; 
x_44 = lean_unsigned_to_nat(13u);
x_45 = lean_uint64_of_nat(x_44);
x_32 = x_45;
goto block_42;
}
else
{
lean_object* x_46; uint64_t x_47; 
x_46 = lean_unsigned_to_nat(11u);
x_47 = lean_uint64_of_nat(x_46);
x_32 = x_47;
goto block_42;
}
block_31:
{
uint64_t x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; lean_object* x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; size_t x_23; size_t x_24; lean_object* x_25; size_t x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; 
x_14 = lean_uint64_mix_hash(x_12, x_13);
x_15 = lean_unsigned_to_nat(32u);
x_16 = lean_uint64_of_nat(x_15);
x_17 = lean_uint64_shift_right(x_14, x_16);
x_18 = lean_uint64_xor(x_14, x_17);
x_19 = lean_unsigned_to_nat(16u);
x_20 = lean_uint64_of_nat(x_19);
x_21 = lean_uint64_shift_right(x_18, x_20);
x_22 = lean_uint64_xor(x_18, x_21);
x_23 = lean_uint64_to_usize(x_22);
x_24 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_usize_of_nat(x_25);
x_27 = lean_usize_sub(x_24, x_26);
x_28 = lean_usize_land(x_23, x_27);
x_29 = lean_array_uget(x_8, x_28);
lean_dec(x_8);
x_30 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1_spec__4___redArg(x_1, x_3, x_29);
return x_30;
}
block_42:
{
lean_object* x_33; uint64_t x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_unsigned_to_nat(7u);
x_34 = lean_uint64_of_nat(x_33);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_array_get_size(x_10);
x_37 = lean_nat_dec_lt(x_35, x_36);
if (x_37 == 0)
{
lean_dec(x_36);
lean_dec(x_10);
x_12 = x_32;
x_13 = x_34;
goto block_31;
}
else
{
uint8_t x_38; 
x_38 = lean_nat_dec_le(x_36, x_36);
if (x_38 == 0)
{
lean_dec(x_36);
lean_dec(x_10);
x_12 = x_32;
x_13 = x_34;
goto block_31;
}
else
{
size_t x_39; size_t x_40; uint64_t x_41; 
x_39 = lean_usize_of_nat(x_35);
x_40 = lean_usize_of_nat(x_36);
lean_dec(x_36);
x_41 = l_Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__0(x_10, x_39, x_40, x_34);
lean_dec(x_10);
x_12 = x_32;
x_13 = x_41;
goto block_31;
}
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint64_t x_53; uint64_t x_54; uint64_t x_73; uint8_t x_84; 
x_48 = lean_ctor_get(x_2, 0);
lean_inc(x_48);
lean_dec(x_2);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_ctor_get(x_3, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_3, 1);
lean_inc(x_51);
x_52 = lean_array_get_size(x_49);
x_84 = lean_unbox(x_50);
lean_dec(x_50);
if (x_84 == 0)
{
lean_object* x_85; uint64_t x_86; 
x_85 = lean_unsigned_to_nat(13u);
x_86 = lean_uint64_of_nat(x_85);
x_73 = x_86;
goto block_83;
}
else
{
lean_object* x_87; uint64_t x_88; 
x_87 = lean_unsigned_to_nat(11u);
x_88 = lean_uint64_of_nat(x_87);
x_73 = x_88;
goto block_83;
}
block_72:
{
uint64_t x_55; lean_object* x_56; uint64_t x_57; uint64_t x_58; uint64_t x_59; lean_object* x_60; uint64_t x_61; uint64_t x_62; uint64_t x_63; size_t x_64; size_t x_65; lean_object* x_66; size_t x_67; size_t x_68; size_t x_69; lean_object* x_70; lean_object* x_71; 
x_55 = lean_uint64_mix_hash(x_53, x_54);
x_56 = lean_unsigned_to_nat(32u);
x_57 = lean_uint64_of_nat(x_56);
x_58 = lean_uint64_shift_right(x_55, x_57);
x_59 = lean_uint64_xor(x_55, x_58);
x_60 = lean_unsigned_to_nat(16u);
x_61 = lean_uint64_of_nat(x_60);
x_62 = lean_uint64_shift_right(x_59, x_61);
x_63 = lean_uint64_xor(x_59, x_62);
x_64 = lean_uint64_to_usize(x_63);
x_65 = lean_usize_of_nat(x_52);
lean_dec(x_52);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_usize_of_nat(x_66);
x_68 = lean_usize_sub(x_65, x_67);
x_69 = lean_usize_land(x_64, x_68);
x_70 = lean_array_uget(x_49, x_69);
lean_dec(x_49);
x_71 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1_spec__4___redArg(x_1, x_3, x_70);
return x_71;
}
block_83:
{
lean_object* x_74; uint64_t x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_74 = lean_unsigned_to_nat(7u);
x_75 = lean_uint64_of_nat(x_74);
x_76 = lean_unsigned_to_nat(0u);
x_77 = lean_array_get_size(x_51);
x_78 = lean_nat_dec_lt(x_76, x_77);
if (x_78 == 0)
{
lean_dec(x_77);
lean_dec(x_51);
x_53 = x_73;
x_54 = x_75;
goto block_72;
}
else
{
uint8_t x_79; 
x_79 = lean_nat_dec_le(x_77, x_77);
if (x_79 == 0)
{
lean_dec(x_77);
lean_dec(x_51);
x_53 = x_73;
x_54 = x_75;
goto block_72;
}
else
{
size_t x_80; size_t x_81; uint64_t x_82; 
x_80 = lean_usize_of_nat(x_76);
x_81 = lean_usize_of_nat(x_77);
lean_dec(x_77);
x_82 = l_Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_Meta_addCustomEliminatorEntry_spec__0_spec__0_spec__0(x_51, x_80, x_81, x_75);
lean_dec(x_51);
x_53 = x_73;
x_54 = x_82;
goto block_72;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminator_x3f(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_mk_empty_array_with_capacity(x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_array_size(x_1);
x_13 = lean_usize_of_nat(x_8);
lean_inc(x_6);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getCustomEliminator_x3f_spec__0(x_1, x_12, x_13, x_11, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_st_ref_get(x_6, x_17);
lean_dec(x_6);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = l_Lean_Name_instBEq;
x_22 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators___redArg___lam__0____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408____boxed), 2, 0);
x_23 = lean_alloc_closure((void*)(l_Array_instBEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_23, 0, x_21);
x_24 = l_Lean_Meta_instInhabitedCustomEliminators;
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_dec(x_15);
x_26 = lean_ctor_get(x_20, 0);
lean_inc(x_26);
lean_dec(x_20);
x_27 = l_instBEqOfDecidableEq___redArg(x_22);
x_28 = l_instBEqProd___redArg(x_27, x_23);
x_29 = l_Lean_Meta_customEliminatorExt;
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get_uint8(x_31, sizeof(void*)*3);
lean_dec(x_31);
x_33 = l_Lean_ScopedEnvExtension_getState___redArg(x_24, x_29, x_26, x_32);
x_34 = lean_box(x_2);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_25);
x_36 = l_Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1___redArg(x_28, x_33, x_35);
lean_ctor_set(x_18, 0, x_36);
return x_18;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_37 = lean_ctor_get(x_18, 0);
x_38 = lean_ctor_get(x_18, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_18);
x_39 = l_Lean_Name_instBEq;
x_40 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprCustomEliminators___redArg___lam__0____x40_Lean_Meta_Tactic_ElimInfo___hyg_2408____boxed), 2, 0);
x_41 = lean_alloc_closure((void*)(l_Array_instBEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_41, 0, x_39);
x_42 = l_Lean_Meta_instInhabitedCustomEliminators;
x_43 = lean_ctor_get(x_15, 1);
lean_inc(x_43);
lean_dec(x_15);
x_44 = lean_ctor_get(x_37, 0);
lean_inc(x_44);
lean_dec(x_37);
x_45 = l_instBEqOfDecidableEq___redArg(x_40);
x_46 = l_instBEqProd___redArg(x_45, x_41);
x_47 = l_Lean_Meta_customEliminatorExt;
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_ctor_get_uint8(x_49, sizeof(void*)*3);
lean_dec(x_49);
x_51 = l_Lean_ScopedEnvExtension_getState___redArg(x_42, x_47, x_44, x_50);
x_52 = lean_box(x_2);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_43);
x_54 = l_Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1___redArg(x_46, x_51, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_38);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec(x_15);
lean_dec(x_6);
x_56 = !lean_is_exclusive(x_14);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_14, 0);
lean_dec(x_57);
x_58 = lean_ctor_get(x_16, 0);
lean_inc(x_58);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_58);
return x_14;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_14, 1);
lean_inc(x_59);
lean_dec(x_14);
x_60 = lean_ctor_get(x_16, 0);
lean_inc(x_60);
lean_dec(x_16);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_6);
x_62 = !lean_is_exclusive(x_14);
if (x_62 == 0)
{
return x_14;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_14, 0);
x_64 = lean_ctor_get(x_14, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_14);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getCustomEliminator_x3f_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getCustomEliminator_x3f_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getCustomEliminator_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getCustomEliminator_x3f_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__1___redArg(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Meta_getCustomEliminator_x3f_spec__1_spec__1_spec__1(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCustomEliminator_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_getCustomEliminator_x3f(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_9;
}
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Check(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ScopedEnvExtension(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_ElimInfo(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Check(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ScopedEnvExtension(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_instReprElimAltInfo = _init_l_Lean_Meta_instReprElimAltInfo();
lean_mark_persistent(l_Lean_Meta_instReprElimAltInfo);
l_Lean_Meta_instInhabitedElimAltInfo = _init_l_Lean_Meta_instInhabitedElimAltInfo();
lean_mark_persistent(l_Lean_Meta_instInhabitedElimAltInfo);
l_Lean_Meta_instReprElimInfo = _init_l_Lean_Meta_instReprElimInfo();
lean_mark_persistent(l_Lean_Meta_instReprElimInfo);
l_Lean_Meta_instInhabitedElimInfo = _init_l_Lean_Meta_instInhabitedElimInfo();
lean_mark_persistent(l_Lean_Meta_instInhabitedElimInfo);
l_Lean_Meta_instInhabitedCustomEliminator = _init_l_Lean_Meta_instInhabitedCustomEliminator();
lean_mark_persistent(l_Lean_Meta_instInhabitedCustomEliminator);
l_Lean_Meta_instReprCustomEliminator = _init_l_Lean_Meta_instReprCustomEliminator();
lean_mark_persistent(l_Lean_Meta_instReprCustomEliminator);
l_Lean_Meta_instInhabitedCustomEliminators = _init_l_Lean_Meta_instInhabitedCustomEliminators();
lean_mark_persistent(l_Lean_Meta_instInhabitedCustomEliminators);
l_Lean_Meta_instReprCustomEliminators = _init_l_Lean_Meta_instReprCustomEliminators();
lean_mark_persistent(l_Lean_Meta_instReprCustomEliminators);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_ElimInfo___hyg_2474_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_customEliminatorExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_customEliminatorExt);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_ElimInfo___hyg_3180_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_ElimInfo___hyg_3258_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
