// Lean compiler output
// Module: Lean.MetavarContext
// Imports: Init.ShareCommon Lean.Util.MonadCache Lean.LocalContext
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
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkAuxMVarType_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_LevelMVarToParam_instMonadMCtxM___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprMetavarKind;
LEAN_EXPORT lean_object* l_Lean_MetavarContext_abstractRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_MetavarKind_isNatural(uint8_t);
uint8_t l_ptrEqList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_withFreshCache___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOnPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instantiateLCtxMVars___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_findDecl_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_getDecl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignedLevelMVar___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkAuxMVarType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVarDeclMVars___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignedLevelMVar___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT uint8_t l_Lean_exprDependsOn_x27___redArg___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_instMonadHashMapCacheAdapterExprStructEqExprM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn_x27___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_LevelMVarToParam_instMonadMCtxM___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_setFVarBinderInfo___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarRoot___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_collectForwardDeps___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_collectForwardDeps___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_forM_loop___at___Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__10_spec__10___redArg___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___redArg___lam__3(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_instMonadMCtxM___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___Lean_MetavarContext_LevelMVarToParam_visitLevel_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_getExprAssignmentDomain(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarRoot(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVarDeclMVars___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_MetavarContext_MkBinding_reduceLocalContext_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_instMonadMCtxM___lam__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_sharecommon_quick(lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_instMonadHashMapCacheAdapterExprStructEqExprM;
LEAN_EXPORT lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
lean_object* l_StateT_get(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_LevelMVarToParam_instMonadMCtxM___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_MVarIdSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_LevelMVarToParam_instMonadCacheExprStructEqExprM;
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadMCtxOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__12_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_mkLambda(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_instToStringException;
LEAN_EXPORT lean_object* l_Lean_MetavarContext_findUserName_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_isWellFormed___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_instMonadMCtxM___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignedOrDelayedAssigned(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_setFVarBinderInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___Lean_MetavarContext_LevelMVarToParam_main_visitApp_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_ExprStructEq_hash___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignedLevelMVar___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_modifyExprMVarDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_reduceLocalContext___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_isWellFormed___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__12_spec__12(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelMax_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_____private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain_spec__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instBEqMVarId;
LEAN_EXPORT lean_object* l_Lean_instantiateMVarDeclMVars___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn_x27___redArg___lam__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_mkLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_revert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_getInScope_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
extern uint8_t l_instInhabitedBool;
LEAN_EXPORT lean_object* l_Lean_MetavarContext_isWellFormed___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_getInScope(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_revert___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_withFreshCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_addLevelMVarDecl(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_LevelMVarToParam_instMonadCacheExprStructEqExprM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at___Lean_MetavarContext_MkBinding_mkBinding_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___redArg___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_withFreshCache(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_hasAssignedLevelMVar___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_modify(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findExprDependsOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_setFVarBinderInfo___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyDecl___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_instMonadMCtxM___lam__0___boxed(lean_object*, lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyLCtx___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignedLevelMVar___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_MetavarContext_LevelMVarToParam_main_visitApp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at_____private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain_spec__1(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_assignLevelMVarExp_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarKind___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_instToStringException___lam__1(lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarKind_isSyntheticOpaque___boxed(lean_object*);
lean_object* l_EStateM_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqLocalInstance___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain_spec__1_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
lean_object* l_instMonadLiftT(lean_object*);
extern lean_object* l_Lean_instInhabitedLocalContext;
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarKind_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_setMVarUserName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___redArg___lam__5(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarBinderInfo___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_isWellFormed___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedLocalInstance;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elim_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkLambda_x27(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findExprDependsOn___redArg___lam__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_elimMVarDeps___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_exprDependsOn_x27___redArg___lam__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarBinderInfo(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkLambda_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DependsOn_main(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarKind_noConfusion___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_instToStringException___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_mkBinding___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instToStringString___lam__0___boxed(lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__0(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3_spec__4___redArg___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__12___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadMCtxStateMMetavarContext;
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_getInScope_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_getExprAssignmentDomain___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_LevelMVarToParam_instMonadMCtxM___lam__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_mkForall(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_assignLevelMVarExp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__12(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
LEAN_EXPORT lean_object* l_Lean_findExprDependsOn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVarDeclMVars___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_getInScope___boxed(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_getFVar_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3_spec__4___redArg___lam__1___boxed(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_MetavarContext_mkBinding_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findLocalDeclDependsOn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_instMonadMCtxM___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssigned___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_elimMVarDeps(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_collectForwardDeps(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_abstractRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLevelMVarAssignment_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssigned(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_setMVarKind___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3_spec__4___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyLCtx___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_getLocalDeclWithSmallestIdx_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instMonadMCtxOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_LevelMVarToParam_main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_eraseAux___at___Lean_PersistentHashMap_erase_spec__0___redArg(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setMCtx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_LevelMVarToParam_visitLevel(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqLocalInstance;
LEAN_EXPORT lean_object* l_Lean_MetavarContext_isWellFormed___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_LevelMVarToParam_instMonadMCtxM___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadMCtxStateRefT_x27MetavarContextST(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_instMonadMCtxM___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_MetavarContext_MkBinding_reduceLocalContext_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_addExprMVarDeclExp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* lean_assign_lmvar(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_assignExp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___Lean_MetavarContext_setMVarUserName_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_getLevelDepth(lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_LevelMVarToParam_instMonadMCtxM;
LEAN_EXPORT lean_object* l_Lean_MetavarContext_addExprMVarDeclExp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_modifyExprMVarLCtx___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_setBinderInfo(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssigned___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___Lean_Expr_appFn_x21_spec__0(lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp_spec__1___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findLocalDeclDependsOn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_MetavarKind_isSyntheticOpaque(uint8_t);
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_instantiate_level_mvars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_isWellFormed___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_assignExp_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__10___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_getExprAssignmentDomain___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__10_spec__10(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkAuxMVarType_abstractRangeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkMVarApp_spec__0(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkMVarApp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at_____private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_instMonadMCtxM___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_MetavarContext_getDecl_spec__0(lean_object*);
lean_object* l_Lean_LocalContext_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__10_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_modifyExprMVarLCtx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignedLevelMVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setMCtx___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_addExprMVarDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setMCtx___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_addExprMVarDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_isWellFormed___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkAuxMVarType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalInstances_erase___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_instMonadMCtxM;
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_isWellFormed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__2(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_reduceLocalContext(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVarDeclMVars___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_MetavarContext_LevelMVarToParam_main_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_dependsOnPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_instHashableLocalInstance___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_find(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_exprDependsOn_x27___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalInstances_erase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_getExprAssignmentCore_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2_spec__2_spec__2___redArg(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOnPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarBinderInfo___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_isWellFormed___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___Lean_MetavarContext_setMVarUserName_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at___Lean_MetavarContext_MkBinding_mkBinding_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Level_0__Lean_hashLevelMVarId____x40_Lean_Level___hyg_522_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_levelMVarToParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_isWellFormed___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_LevelMVarToParam_mkParamName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_instMonadHashMapCacheAdapterExprStructEqExprM___lam__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Level_0__Lean_hashLevelMVarId____x40_Lean_Level___hyg_522____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_MetavarContext_mkBinding_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_collectForwardDeps(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_anyTR_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_revert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_getExprAssignmentCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_MetavarContext_isAnonymousMVar(lean_object*, lean_object*);
uint8_t l_Lean_LocalContext_contains(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_simpLevelIMax_x27(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isLet(lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findExprDependsOn___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_mkBinding(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarKind___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_expr_lift_loose_bvars(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_assign_mvar(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_lower_loose_bvars(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_elimMVarDeps(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_preserveOrder(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_dependsOn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_abstractRange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Expr_0__Lean_hashMVarId____x40_Lean_Expr___hyg_1984_(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_MetavarContext_LevelMVarToParam_main_visitApp_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarKind(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instInhabitedMetavarDecl;
LEAN_EXPORT lean_object* l_Lean_MetavarKind_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarKind_noConfusion___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instHashableMVarId;
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarKind___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_LevelMVarToParam_instMonadMCtxM___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findExprDependsOn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_LevelMVarToParam_instMonadMCtxM___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLevelMVarAssignment_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_withFreshCache___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_MetavarContext_LevelMVarToParam_main_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DependsOn_instMonadMCtxM___lam__1(lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_findDecl_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_DependsOn_instMonadMCtxM;
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__10_spec__10___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_preserveOrder___boxed(lean_object*, lean_object*);
lean_object* l_List_anyM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__12_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalContext_isSubPrefixOf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_anyTR_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_isWellFormed___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_runST___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_mkBinding___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_setFVarBinderInfo(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_instMonadMCtxM___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findLocalDeclDependsOn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___redArg___lam__1___boxed(lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarKind_noConfusion___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elim_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_setKind(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkAuxMVarType_abstractRangeAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignedLevelMVar___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_get_lmvar_assignment(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashableLocalInstance___lam__0___boxed(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___Lean_MetavarContext_LevelMVarToParam_main_visitApp_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_mk_metavar_ctx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyDecl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_findLevelDepth_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_getExprAssignmentDomain___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_mkBinding(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elim(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DependsOn_instMonadMCtxM___lam__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instantiateLCtxMVars___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarKind___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarBinderInfo___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* l_ReaderT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain_spec__1_spec__1_spec__1(uint8_t, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkAuxMVarType_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashableLocalInstance;
LEAN_EXPORT lean_object* l_Lean_MetavarContext_isAnonymousMVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instInhabitedMetavarContext;
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__10(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignedLevelMVar___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_local_ctx_erase(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT uint8_t l_Lean_instInhabitedMetavarKind;
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at_____private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain_spec__0___boxed(lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_ExprStructEq_instBEq;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_isWellFormed___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadStateOfMonadStateOf___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarKind_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_dependsOnPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___Lean_MetavarContext_LevelMVarToParam_main_visitApp_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadLift(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_LevelMVarToParam_main_visitApp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_LevelMVarToParam_instMonadMCtxM___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___Lean_MetavarContext_LevelMVarToParam_visitLevel_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_incDepth___boxed(lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findLocalDeclDependsOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_setMVarType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__10_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instantiateMVarDeclMVars(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVarDeclMVars___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignedLevelMVar___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_findExprDependsOn___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignedLevelMVar___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_LevelMVarToParam_instMonadCacheExprStructEqExprM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findExprDependsOn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkAuxMVarType(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalInstances_erase___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVarsCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_instInhabitedEntry(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___Lean_MetavarContext_LevelMVarToParam_main_visitApp_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVarsImp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___Lean_MetavarContext_LevelMVarToParam_visitLevel_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString(lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkAuxDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_instToStringException___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_getLocalDeclWithSmallestIdx_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarBinderInfo___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_isWellFormed___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_LevelMVarToParam_instMonadCacheExprStructEqExprM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instBEqLevelMVarId;
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_findLevelDepth_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_instMonadHashMapCacheAdapterExprStructEqExprM___lam__0(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_LevelMVarToParam_instMonadCacheExprStructEqExprM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarRoot___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkFreshBinderName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at___Lean_MetavarContext_MkBinding_mkBinding_spec__0___redArg(lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_getLocalDeclWithSmallestIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarKind_isNatural___boxed(lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain_spec__1_spec__1(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_setFVarKind(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_setFVarKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_getLevelDepth___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp_spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_findUserName_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_elimMVarDeps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_mkForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* l_instMonadStateOfStateTOfMonad___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_setMVarKind(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkAuxMVarType_spec__0___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignedLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_abstractRange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkMVarApp(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_LevelMVarToParam_instMonadMCtxM___lam__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
extern lean_object* l_Lean_Name_instBEq;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* lean_instantiate_expr_mvars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn_x27___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__12_spec__12___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_get_mvar_assignment(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyLCtx(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_dependsOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setMCtx___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_LevelMVarToParam_instMonadMCtxM___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_simpLevelMax_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at___Lean_MetavarContext_MkBinding_mkBinding_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Array_eraseP___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instBEqLocalInstance___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_isWellFormed___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarKind_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___String_toNat_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVarsImp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DependsOn_instMonadMCtxM___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_get_delayed_mvar_assignment(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignedOrDelayedAssigned___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_isWellFormed___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_setFVarKind___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain_spec__1_spec__1_spec__2(uint8_t, lean_object*, lean_object*, size_t, size_t);
uint8_t l_Lean_Expr_isFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_incDepth(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_instMonadHashMapCacheAdapterExprStructEqExprM___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkMVarApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignedOrDelayedAssigned___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_reprMetavarKind____x40_Lean_MetavarContext___hyg_108____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_setFVarKind___lam__0(lean_object*, uint8_t, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___redArg___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_isWellFormed___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_anyTR_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__10_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_MetavarKind_noConfusion___redArg(uint8_t, uint8_t);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_isWellFormed___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_anyTR_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLevelMVarAssignment_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_instMonadMCtxM___lam__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instHashableName;
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarBinderInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_reprMetavarKind____x40_Lean_MetavarContext___hyg_108_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MetavarContext_setMVarUserNameTemporarily(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_instInhabitedLocalInstance() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(0);
x_5 = l_Lean_Expr_const___override(x_3, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqLocalInstance___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_expr_eqv(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_instBEqLocalInstance() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instBEqLocalInstance___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqLocalInstance___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_instBEqLocalInstance___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableLocalInstance___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint64_t x_3; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = l_Lean_Expr_hash(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instHashableLocalInstance() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instHashableLocalInstance___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableLocalInstance___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_instHashableLocalInstance___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalInstances_erase___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = l_Lean_Expr_fvarId_x21(x_3);
x_5 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_4, x_1);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalInstances_erase(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_LocalInstances_erase___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Array_eraseP___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalInstances_erase___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_LocalInstances_erase___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarKind_toCtorIdx(uint8_t x_1) {
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
LEAN_EXPORT lean_object* l_Lean_MetavarKind_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_MetavarKind_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarKind_noConfusion___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarKind_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_MetavarKind_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarKind_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MetavarKind_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarKind_noConfusion___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MetavarKind_noConfusion___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarKind_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_MetavarKind_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarKind_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_MetavarKind_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
static uint8_t _init_l_Lean_instInhabitedMetavarKind() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_unbox(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_reprMetavarKind____x40_Lean_MetavarContext___hyg_108_(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_12; lean_object* x_21; 
switch (x_1) {
case 0:
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_unsigned_to_nat(1024u);
x_31 = lean_nat_dec_le(x_30, x_2);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_unsigned_to_nat(2u);
x_33 = lean_nat_to_int(x_32);
x_3 = x_33;
goto block_11;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_to_int(x_34);
x_3 = x_35;
goto block_11;
}
}
case 1:
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_unsigned_to_nat(1024u);
x_37 = lean_nat_dec_le(x_36, x_2);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_unsigned_to_nat(2u);
x_39 = lean_nat_to_int(x_38);
x_12 = x_39;
goto block_20;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_to_int(x_40);
x_12 = x_41;
goto block_20;
}
}
default: 
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_unsigned_to_nat(1024u);
x_43 = lean_nat_dec_le(x_42, x_2);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_unsigned_to_nat(2u);
x_45 = lean_nat_to_int(x_44);
x_21 = x_45;
goto block_29;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_to_int(x_46);
x_21 = x_47;
goto block_29;
}
}
}
block_11:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_4 = lean_mk_string_unchecked("Lean.MetavarKind.natural", 24, 24);
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
x_13 = lean_mk_string_unchecked("Lean.MetavarKind.synthetic", 26, 26);
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
block_29:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_22 = lean_mk_string_unchecked("Lean.MetavarKind.syntheticOpaque", 32, 32);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_26, 0, x_24);
x_27 = lean_unbox(x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_27);
x_28 = l_Repr_addAppParen(x_26, x_2);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_reprMetavarKind____x40_Lean_MetavarContext___hyg_108____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l___private_Lean_MetavarContext_0__Lean_reprMetavarKind____x40_Lean_MetavarContext___hyg_108_(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_instReprMetavarKind() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_MetavarContext_0__Lean_reprMetavarKind____x40_Lean_MetavarContext___hyg_108____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_MetavarKind_isSyntheticOpaque(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(x_1);
if (lean_obj_tag(x_2) == 2)
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
}
LEAN_EXPORT lean_object* l_Lean_MetavarKind_isSyntheticOpaque___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_MetavarKind_isSyntheticOpaque(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_MetavarKind_isNatural(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(x_1);
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
}
LEAN_EXPORT lean_object* l_Lean_MetavarKind_isNatural___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_MetavarKind_isNatural(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_instInhabitedMetavarDecl() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_1 = lean_box(0);
x_2 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = l_Array_empty(lean_box(0));
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_box(0);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_usize_of_nat(x_7);
lean_inc(x_4);
x_9 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_6);
lean_ctor_set_usize(x_9, 4, x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_10);
x_12 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_box(0);
x_15 = l_Lean_Expr_const___override(x_13, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_15);
lean_ctor_set(x_17, 3, x_6);
lean_ctor_set(x_17, 4, x_4);
lean_ctor_set(x_17, 5, x_6);
lean_ctor_set(x_17, 6, x_6);
x_18 = lean_unbox(x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*7, x_18);
return x_17;
}
}
static lean_object* _init_l_Lean_instInhabitedMetavarContext() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
lean_inc(x_2);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_2);
lean_inc(x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_2);
lean_inc(x_2);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_2);
lean_inc(x_2);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_2);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_2);
x_9 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_1);
lean_ctor_set(x_9, 2, x_1);
lean_ctor_set(x_9, 3, x_3);
lean_ctor_set(x_9, 4, x_4);
lean_ctor_set(x_9, 5, x_5);
lean_ctor_set(x_9, 6, x_6);
lean_ctor_set(x_9, 7, x_7);
lean_ctor_set(x_9, 8, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_instMonadMCtxStateMMetavarContext() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_2 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_3 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_4 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_5 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_6 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_7 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_2);
x_9 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
lean_ctor_set(x_9, 2, x_4);
lean_ctor_set(x_9, 3, x_5);
lean_ctor_set(x_9, 4, x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
lean_inc(x_10);
x_11 = l_instMonadStateOfStateTOfMonad___redArg(x_10);
x_12 = l_instMonadStateOfMonadStateOf___redArg(x_11);
x_13 = lean_alloc_closure((void*)(l_StateT_get), 4, 3);
lean_closure_set(x_13, 0, lean_box(0));
lean_closure_set(x_13, 1, lean_box(0));
lean_closure_set(x_13, 2, x_10);
x_14 = lean_alloc_closure((void*)(l_modify), 4, 3);
lean_closure_set(x_14, 0, lean_box(0));
lean_closure_set(x_14, 1, lean_box(0));
lean_closure_set(x_14, 2, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_4, x_3);
x_6 = lean_apply_2(x_2, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadMCtxOfMonadLift___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_1);
lean_inc(x_2);
x_3 = lean_alloc_closure((void*)(l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadMCtxOfMonadLift(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_3);
lean_inc(x_4);
x_5 = lean_alloc_closure((void*)(l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_2(x_3, lean_box(0), x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_setMCtx___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_setMCtx___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lean_setMCtx___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_setMCtx(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Lean_setMCtx___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_apply_1(x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_setMCtx___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_setMCtx___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_getLevelMVarAssignment_x3f___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 6);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_PersistentHashMap_find_x3f___redArg(x_1, x_2, x_6, x_3);
x_8 = lean_apply_2(x_4, lean_box(0), x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_getLevelMVarAssignment_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = l_Lean_instBEqLevelMVarId;
x_5 = lean_alloc_closure((void*)(l___private_Lean_Level_0__Lean_hashLevelMVarId____x40_Lean_Level___hyg_522____boxed), 1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_getLevelMVarAssignment_x3f___redArg___lam__0), 5, 4);
lean_closure_set(x_10, 0, x_4);
lean_closure_set(x_10, 1, x_5);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_9);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_getLevelMVarAssignment_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = l_Lean_instBEqLevelMVarId;
x_6 = lean_alloc_closure((void*)(l___private_Lean_Level_0__Lean_hashLevelMVarId____x40_Lean_Level___hyg_522____boxed), 1, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_getLevelMVarAssignment_x3f___redArg___lam__0), 5, 4);
lean_closure_set(x_11, 0, x_5);
lean_closure_set(x_11, 1, x_6);
lean_closure_set(x_11, 2, x_4);
lean_closure_set(x_11, 3, x_10);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget(x_1, x_3);
x_9 = lean_name_eq(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget(x_2, x_3);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0_spec__0_spec__0___redArg(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; size_t x_10; size_t x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Lean_PersistentHashMap_instInhabitedEntry(lean_box(0), lean_box(0), lean_box(0));
x_7 = lean_unsigned_to_nat(5u);
x_8 = lean_usize_of_nat(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_shift_left(x_10, x_8);
x_12 = lean_usize_sub(x_11, x_10);
x_13 = lean_usize_land(x_2, x_12);
x_14 = lean_usize_to_nat(x_13);
x_15 = lean_array_get(x_6, x_5, x_14);
lean_dec(x_14);
lean_dec(x_5);
switch (lean_obj_tag(x_15)) {
case 0:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_name_eq(x_3, x_16);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_17);
lean_free_object(x_1);
x_19 = lean_box(0);
return x_19;
}
else
{
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_17);
return x_1;
}
}
case 1:
{
lean_object* x_20; size_t x_21; 
lean_free_object(x_1);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_usize_shift_right(x_2, x_8);
x_1 = x_20;
x_2 = x_21;
goto _start;
}
default: 
{
lean_object* x_23; 
lean_free_object(x_1);
x_23 = lean_box(0);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; lean_object* x_28; size_t x_29; size_t x_30; size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
lean_dec(x_1);
x_25 = l_Lean_PersistentHashMap_instInhabitedEntry(lean_box(0), lean_box(0), lean_box(0));
x_26 = lean_unsigned_to_nat(5u);
x_27 = lean_usize_of_nat(x_26);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_usize_of_nat(x_28);
x_30 = lean_usize_shift_left(x_29, x_27);
x_31 = lean_usize_sub(x_30, x_29);
x_32 = lean_usize_land(x_2, x_31);
x_33 = lean_usize_to_nat(x_32);
x_34 = lean_array_get(x_25, x_24, x_33);
lean_dec(x_33);
lean_dec(x_24);
switch (lean_obj_tag(x_34)) {
case 0:
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_name_eq(x_3, x_35);
lean_dec(x_35);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_36);
x_38 = lean_box(0);
return x_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_36);
return x_39;
}
}
case 1:
{
lean_object* x_40; size_t x_41; 
x_40 = lean_ctor_get(x_34, 0);
lean_inc(x_40);
lean_dec(x_34);
x_41 = lean_usize_shift_right(x_2, x_27);
x_1 = x_40;
x_2 = x_41;
goto _start;
}
default: 
{
lean_object* x_43; 
x_43 = lean_box(0);
return x_43;
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
lean_dec(x_1);
x_46 = lean_unsigned_to_nat(0u);
x_47 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0_spec__0_spec__0___redArg(x_44, x_45, x_46, x_3);
lean_dec(x_45);
lean_dec(x_44);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l___private_Lean_Level_0__Lean_hashLevelMVarId____x40_Lean_Level___hyg_522_(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0_spec__0___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lean_get_lmvar_assignment(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 6);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0___redArg(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0_spec__0___redArg(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0_spec__0(x_1, x_2, x_5, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget(x_1, x_3);
x_9 = lean_name_eq(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget(x_2, x_3);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0_spec__0_spec__0___redArg(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; size_t x_10; size_t x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Lean_PersistentHashMap_instInhabitedEntry(lean_box(0), lean_box(0), lean_box(0));
x_7 = lean_unsigned_to_nat(5u);
x_8 = lean_usize_of_nat(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_shift_left(x_10, x_8);
x_12 = lean_usize_sub(x_11, x_10);
x_13 = lean_usize_land(x_2, x_12);
x_14 = lean_usize_to_nat(x_13);
x_15 = lean_array_get(x_6, x_5, x_14);
lean_dec(x_14);
lean_dec(x_5);
switch (lean_obj_tag(x_15)) {
case 0:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_name_eq(x_3, x_16);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_17);
lean_free_object(x_1);
x_19 = lean_box(0);
return x_19;
}
else
{
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_17);
return x_1;
}
}
case 1:
{
lean_object* x_20; size_t x_21; 
lean_free_object(x_1);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_usize_shift_right(x_2, x_8);
x_1 = x_20;
x_2 = x_21;
goto _start;
}
default: 
{
lean_object* x_23; 
lean_free_object(x_1);
x_23 = lean_box(0);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; lean_object* x_28; size_t x_29; size_t x_30; size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
lean_dec(x_1);
x_25 = l_Lean_PersistentHashMap_instInhabitedEntry(lean_box(0), lean_box(0), lean_box(0));
x_26 = lean_unsigned_to_nat(5u);
x_27 = lean_usize_of_nat(x_26);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_usize_of_nat(x_28);
x_30 = lean_usize_shift_left(x_29, x_27);
x_31 = lean_usize_sub(x_30, x_29);
x_32 = lean_usize_land(x_2, x_31);
x_33 = lean_usize_to_nat(x_32);
x_34 = lean_array_get(x_25, x_24, x_33);
lean_dec(x_33);
lean_dec(x_24);
switch (lean_obj_tag(x_34)) {
case 0:
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_name_eq(x_3, x_35);
lean_dec(x_35);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_36);
x_38 = lean_box(0);
return x_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_36);
return x_39;
}
}
case 1:
{
lean_object* x_40; size_t x_41; 
x_40 = lean_ctor_get(x_34, 0);
lean_inc(x_40);
lean_dec(x_34);
x_41 = lean_usize_shift_right(x_2, x_27);
x_1 = x_40;
x_2 = x_41;
goto _start;
}
default: 
{
lean_object* x_43; 
x_43 = lean_box(0);
return x_43;
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
lean_dec(x_1);
x_46 = lean_unsigned_to_nat(0u);
x_47 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0_spec__0_spec__0___redArg(x_44, x_45, x_46, x_3);
lean_dec(x_45);
lean_dec(x_44);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l___private_Lean_Expr_0__Lean_hashMVarId____x40_Lean_Expr___hyg_1984_(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0_spec__0___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_getExprAssignmentCore_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 7);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0___redArg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0_spec__0___redArg(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0_spec__0(x_1, x_2, x_5, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_getExprAssignmentCore_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MetavarContext_getExprAssignmentCore_x3f(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_get_mvar_assignment(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 7);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0___redArg(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_MetavarContext_getExprAssignmentCore_x3f(x_3, x_1);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_getExprMVarAssignment_x3f___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_7);
x_9 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getExprMVarAssignment_x3f___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getExprMVarAssignment_x3f___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 8);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0___redArg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_get_delayed_mvar_assignment(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 8);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0___redArg(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(x_3, x_1);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_getDelayedMVarAssignment_x3f___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_7);
x_9 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getDelayedMVarAssignment_x3f___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getDelayedMVarAssignment_x3f___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarRoot___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_apply_2(x_1, lean_box(0), x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_getDelayedMVarRoot___redArg(x_3, x_4, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarRoot___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_getDelayedMVarAssignment_x3f___redArg(x_1, x_2, x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_getDelayedMVarRoot___redArg___lam__0), 5, 4);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_3);
lean_closure_set(x_8, 2, x_1);
lean_closure_set(x_8, 3, x_2);
x_9 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarRoot(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getDelayedMVarRoot___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssigned___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 6);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_PersistentHashMap_contains(lean_box(0), lean_box(0), x_1, x_2, x_6, x_3);
x_8 = lean_box(x_7);
x_9 = lean_apply_2(x_4, lean_box(0), x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssigned___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = l_Lean_instBEqLevelMVarId;
x_5 = lean_alloc_closure((void*)(l___private_Lean_Level_0__Lean_hashLevelMVarId____x40_Lean_Level___hyg_522____boxed), 1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_isLevelMVarAssigned___redArg___lam__0), 5, 4);
lean_closure_set(x_10, 0, x_4);
lean_closure_set(x_10, 1, x_5);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_9);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssigned(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isLevelMVarAssigned___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 7);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_PersistentHashMap_contains(lean_box(0), lean_box(0), x_1, x_2, x_6, x_3);
x_8 = lean_box(x_7);
x_9 = lean_apply_2(x_4, lean_box(0), x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = l_Lean_instBEqMVarId;
x_5 = l_Lean_instHashableMVarId;
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_MVarId_isAssigned___redArg___lam__0), 5, 4);
lean_closure_set(x_10, 0, x_4);
lean_closure_set(x_10, 1, x_5);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_9);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MVarId_isAssigned___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 8);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_PersistentHashMap_contains(lean_box(0), lean_box(0), x_1, x_2, x_6, x_3);
x_8 = lean_box(x_7);
x_9 = lean_apply_2(x_4, lean_box(0), x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = l_Lean_instBEqMVarId;
x_5 = l_Lean_instHashableMVarId;
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_MVarId_isDelayedAssigned___redArg___lam__0), 5, 4);
lean_closure_set(x_10, 0, x_4);
lean_closure_set(x_10, 1, x_5);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_9);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MVarId_isDelayedAssigned___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignedOrDelayedAssigned___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 7);
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_PersistentHashMap_contains(lean_box(0), lean_box(0), x_1, x_2, x_6, x_3);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_5, 8);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_Lean_PersistentHashMap_contains(lean_box(0), lean_box(0), x_1, x_2, x_8, x_3);
x_10 = lean_box(x_9);
x_11 = lean_apply_2(x_4, lean_box(0), x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(x_7);
x_13 = lean_apply_2(x_4, lean_box(0), x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignedOrDelayedAssigned___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = l_Lean_instBEqMVarId;
x_5 = l_Lean_instHashableMVarId;
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_MVarId_isAssignedOrDelayedAssigned___redArg___lam__0), 5, 4);
lean_closure_set(x_10, 0, x_4);
lean_closure_set(x_10, 1, x_5);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_9);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignedOrDelayedAssigned(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MVarId_isAssignedOrDelayedAssigned___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
x_8 = l_Lean_PersistentHashMap_find_x3f___redArg(x_1, x_2, x_7, x_3);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_5);
x_9 = lean_mk_string_unchecked("Lean.MetavarContext", 19, 19);
x_10 = lean_mk_string_unchecked("Lean.isLevelMVarAssignable", 26, 26);
x_11 = lean_unsigned_to_nat(425u);
x_12 = lean_unsigned_to_nat(14u);
x_13 = lean_mk_string_unchecked("unknown universe metavariable", 29, 29);
x_14 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
x_15 = l_panic___redArg(x_4, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
lean_dec(x_8);
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_dec(x_6);
x_18 = lean_nat_dec_le(x_17, x_16);
lean_dec(x_16);
lean_dec(x_17);
x_19 = lean_box(x_18);
x_20 = lean_apply_2(x_5, lean_box(0), x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_4 = l_instInhabitedBool;
x_5 = l_Lean_instBEqLevelMVarId;
x_6 = lean_alloc_closure((void*)(l___private_Lean_Level_0__Lean_hashLevelMVarId____x40_Lean_Level___hyg_522____boxed), 1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(x_4);
x_12 = l_instInhabitedOfMonad___redArg(x_1, x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_isLevelMVarAssignable___redArg___lam__0), 6, 5);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_6);
lean_closure_set(x_13, 2, x_3);
lean_closure_set(x_13, 3, x_12);
lean_closure_set(x_13, 4, x_10);
x_14 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isLevelMVarAssignable___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_MetavarContext_getDecl_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedMetavarDecl;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_getDecl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 4);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0___redArg(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_mk_string_unchecked("Lean.MetavarContext", 19, 19);
x_6 = lean_mk_string_unchecked("Lean.MetavarContext.getDecl", 27, 27);
x_7 = lean_unsigned_to_nat(430u);
x_8 = lean_unsigned_to_nat(17u);
x_9 = lean_mk_string_unchecked("unknown metavariable", 20, 20);
x_10 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_11 = l_panic___at___Lean_MetavarContext_getDecl_spec__0(x_10);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
lean_dec(x_4);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_getDecl___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MetavarContext_getDecl(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_3);
x_4 = l_Lean_MetavarContext_getDecl(x_3, x_1);
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_nat_dec_eq(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
x_8 = lean_box(x_7);
x_9 = lean_apply_2(x_2, lean_box(0), x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_MVarId_isAssignable___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_7);
x_9 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MVarId_isAssignable___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MVarId_isAssignable___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedLevelMVar___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = l_Lean_hasAssignedLevelMVar___redArg(x_2, x_3, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedLevelMVar___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Level_hasMVar(x_1);
x_7 = lean_box(x_6);
x_8 = lean_apply_2(x_2, lean_box(0), x_7);
x_9 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_box(x_5);
x_11 = lean_apply_2(x_2, lean_box(0), x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedLevelMVar___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = l_Lean_hasAssignedLevelMVar___redArg(x_2, x_3, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedLevelMVar___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_hasAssignedLevelMVar___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_3);
lean_closure_set(x_7, 3, x_6);
lean_inc(x_4);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_hasAssignedLevelMVar___redArg___lam__1___boxed), 5, 4);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, x_4);
lean_closure_set(x_8, 3, x_7);
lean_inc(x_5);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_hasAssignedLevelMVar___redArg___lam__2___boxed), 5, 4);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_3);
lean_closure_set(x_9, 3, x_5);
x_10 = l_Lean_Level_hasMVar(x_5);
lean_dec(x_5);
x_11 = lean_box(x_10);
x_12 = lean_apply_2(x_1, lean_box(0), x_11);
lean_inc(x_4);
x_13 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_12, x_9);
x_14 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_13, x_8);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedLevelMVar___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = l_Lean_hasAssignedLevelMVar___redArg(x_2, x_3, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedLevelMVar___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
lean_inc(x_7);
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_hasAssignedLevelMVar___redArg___lam__4___boxed), 5, 4);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, x_2);
lean_closure_set(x_8, 3, x_7);
x_9 = l_Lean_Level_hasMVar(x_7);
lean_dec(x_7);
x_10 = lean_box(x_9);
x_11 = lean_apply_2(x_6, lean_box(0), x_10);
x_12 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_11, x_8);
return x_12;
}
case 2:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
lean_dec(x_3);
x_18 = l_Lean_hasAssignedLevelMVar___redArg___lam__3(x_15, x_1, x_2, x_13, x_16, x_17);
return x_18;
}
case 3:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_3, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_3, 1);
lean_inc(x_23);
lean_dec(x_3);
x_24 = l_Lean_hasAssignedLevelMVar___redArg___lam__3(x_21, x_1, x_2, x_19, x_22, x_23);
return x_24;
}
case 5:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_3, 0);
lean_inc(x_25);
lean_dec(x_3);
x_26 = l_Lean_isLevelMVarAssigned___redArg(x_1, x_2, x_25);
return x_26;
}
default: 
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_box(0);
x_30 = lean_apply_2(x_28, lean_box(0), x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedLevelMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_hasAssignedLevelMVar___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedLevelMVar___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_hasAssignedLevelMVar___redArg___lam__0(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedLevelMVar___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_hasAssignedLevelMVar___redArg___lam__1(x_1, x_2, x_3, x_4, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedLevelMVar___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_hasAssignedLevelMVar___redArg___lam__2(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedLevelMVar___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_hasAssignedLevelMVar___redArg___lam__4(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = l_Lean_hasAssignedMVar___redArg(x_2, x_3, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Expr_hasMVar(x_1);
x_7 = lean_box(x_6);
x_8 = lean_apply_2(x_2, lean_box(0), x_7);
x_9 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_box(x_5);
x_11 = lean_apply_2(x_2, lean_box(0), x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = l_Lean_hasAssignedMVar___redArg(x_2, x_3, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_hasAssignedMVar___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_3);
lean_closure_set(x_9, 3, x_7);
lean_inc(x_4);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_hasAssignedMVar___redArg___lam__1___boxed), 5, 4);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_1);
lean_closure_set(x_10, 2, x_4);
lean_closure_set(x_10, 3, x_9);
lean_inc(x_6);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_hasAssignedMVar___redArg___lam__2___boxed), 5, 4);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_6);
x_12 = l_Lean_Expr_hasMVar(x_6);
lean_dec(x_6);
x_13 = lean_box(x_12);
x_14 = lean_apply_2(x_1, lean_box(0), x_13);
lean_inc(x_4);
x_15 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_14, x_11);
x_16 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_15, x_10);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
x_6 = l_Lean_MVarId_isDelayedAssigned___redArg(x_1, x_2, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_5);
x_8 = lean_apply_2(x_4, lean_box(0), x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = l_Lean_hasAssignedMVar___redArg(x_2, x_3, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Expr_hasMVar(x_1);
x_7 = lean_box(x_6);
x_8 = lean_apply_2(x_2, lean_box(0), x_7);
x_9 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_box(x_5);
x_11 = lean_apply_2(x_2, lean_box(0), x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = l_Lean_hasAssignedMVar___redArg(x_2, x_3, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = l_Lean_hasAssignedMVar___redArg(x_2, x_3, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Expr_hasMVar(x_1);
x_7 = lean_box(x_6);
x_8 = lean_apply_2(x_2, lean_box(0), x_7);
x_9 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_box(x_5);
x_11 = lean_apply_2(x_2, lean_box(0), x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = l_Lean_hasAssignedMVar___redArg(x_2, x_3, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
if (x_6 == 0)
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_Expr_hasMVar(x_1);
x_8 = lean_box(x_7);
x_9 = lean_apply_2(x_2, lean_box(0), x_8);
lean_inc(x_3);
x_10 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_9, x_4);
x_11 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_10, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_box(x_6);
x_13 = lean_apply_2(x_2, lean_box(0), x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = l_Lean_hasAssignedMVar___redArg(x_2, x_3, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = l_Lean_hasAssignedMVar___redArg(x_2, x_3, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = l_Lean_hasAssignedMVar___redArg(x_2, x_3, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 2:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_hasAssignedMVar___redArg___lam__4___boxed), 5, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_7);
lean_closure_set(x_8, 3, x_6);
x_9 = l_Lean_MVarId_isAssigned___redArg(x_1, x_2, x_7);
x_10 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_9, x_8);
return x_10;
}
case 3:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
x_12 = l_Lean_hasAssignedLevelMVar___redArg(x_1, x_2, x_11);
return x_12;
}
case 4:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_dec(x_3);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_hasAssignedLevelMVar), 4, 3);
lean_closure_set(x_14, 0, lean_box(0));
lean_closure_set(x_14, 1, x_1);
lean_closure_set(x_14, 2, x_2);
x_15 = l_List_anyM___redArg(x_1, x_14, x_13);
return x_15;
}
case 5:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_3, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
lean_dec(x_3);
lean_inc(x_20);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_18);
x_21 = lean_alloc_closure((void*)(l_Lean_hasAssignedMVar___redArg___lam__5___boxed), 5, 4);
lean_closure_set(x_21, 0, x_18);
lean_closure_set(x_21, 1, x_1);
lean_closure_set(x_21, 2, x_2);
lean_closure_set(x_21, 3, x_20);
lean_inc(x_16);
lean_inc(x_18);
x_22 = lean_alloc_closure((void*)(l_Lean_hasAssignedMVar___redArg___lam__6___boxed), 5, 4);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_18);
lean_closure_set(x_22, 2, x_16);
lean_closure_set(x_22, 3, x_21);
lean_inc(x_19);
lean_inc(x_18);
x_23 = lean_alloc_closure((void*)(l_Lean_hasAssignedMVar___redArg___lam__7___boxed), 5, 4);
lean_closure_set(x_23, 0, x_18);
lean_closure_set(x_23, 1, x_1);
lean_closure_set(x_23, 2, x_2);
lean_closure_set(x_23, 3, x_19);
x_24 = l_Lean_Expr_hasMVar(x_19);
lean_dec(x_19);
x_25 = lean_box(x_24);
x_26 = lean_apply_2(x_18, lean_box(0), x_25);
lean_inc(x_16);
x_27 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_26, x_23);
x_28 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_27, x_22);
return x_28;
}
case 6:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get(x_3, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_3, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_3, 2);
lean_inc(x_34);
x_35 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_dec(x_3);
x_36 = l_Lean_hasAssignedMVar___redArg___lam__3(x_31, x_1, x_2, x_29, x_32, x_33, x_34, x_35);
lean_dec(x_32);
return x_36;
}
case 7:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_ctor_get(x_3, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_3, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_3, 2);
lean_inc(x_42);
x_43 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_dec(x_3);
x_44 = l_Lean_hasAssignedMVar___redArg___lam__3(x_39, x_1, x_2, x_37, x_40, x_41, x_42, x_43);
lean_dec(x_40);
return x_44;
}
case 8:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_1, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_ctor_get(x_3, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_3, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_3, 3);
lean_inc(x_50);
lean_dec(x_3);
lean_inc(x_50);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_47);
x_51 = lean_alloc_closure((void*)(l_Lean_hasAssignedMVar___redArg___lam__8___boxed), 5, 4);
lean_closure_set(x_51, 0, x_47);
lean_closure_set(x_51, 1, x_1);
lean_closure_set(x_51, 2, x_2);
lean_closure_set(x_51, 3, x_50);
lean_inc(x_45);
lean_inc(x_47);
x_52 = lean_alloc_closure((void*)(l_Lean_hasAssignedMVar___redArg___lam__9___boxed), 5, 4);
lean_closure_set(x_52, 0, x_50);
lean_closure_set(x_52, 1, x_47);
lean_closure_set(x_52, 2, x_45);
lean_closure_set(x_52, 3, x_51);
lean_inc(x_49);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_47);
x_53 = lean_alloc_closure((void*)(l_Lean_hasAssignedMVar___redArg___lam__10___boxed), 5, 4);
lean_closure_set(x_53, 0, x_47);
lean_closure_set(x_53, 1, x_1);
lean_closure_set(x_53, 2, x_2);
lean_closure_set(x_53, 3, x_49);
lean_inc(x_45);
lean_inc(x_47);
x_54 = lean_alloc_closure((void*)(l_Lean_hasAssignedMVar___redArg___lam__11___boxed), 6, 5);
lean_closure_set(x_54, 0, x_49);
lean_closure_set(x_54, 1, x_47);
lean_closure_set(x_54, 2, x_45);
lean_closure_set(x_54, 3, x_53);
lean_closure_set(x_54, 4, x_52);
lean_inc(x_48);
lean_inc(x_47);
x_55 = lean_alloc_closure((void*)(l_Lean_hasAssignedMVar___redArg___lam__12___boxed), 5, 4);
lean_closure_set(x_55, 0, x_47);
lean_closure_set(x_55, 1, x_1);
lean_closure_set(x_55, 2, x_2);
lean_closure_set(x_55, 3, x_48);
x_56 = l_Lean_Expr_hasMVar(x_48);
lean_dec(x_48);
x_57 = lean_box(x_56);
x_58 = lean_apply_2(x_47, lean_box(0), x_57);
lean_inc(x_45);
x_59 = lean_apply_4(x_45, lean_box(0), lean_box(0), x_58, x_55);
x_60 = lean_apply_4(x_45, lean_box(0), lean_box(0), x_59, x_54);
return x_60;
}
case 10:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_61 = lean_ctor_get(x_1, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_1, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_ctor_get(x_3, 1);
lean_inc(x_64);
lean_dec(x_3);
lean_inc(x_64);
lean_inc(x_63);
x_65 = lean_alloc_closure((void*)(l_Lean_hasAssignedMVar___redArg___lam__13___boxed), 5, 4);
lean_closure_set(x_65, 0, x_63);
lean_closure_set(x_65, 1, x_1);
lean_closure_set(x_65, 2, x_2);
lean_closure_set(x_65, 3, x_64);
x_66 = l_Lean_Expr_hasMVar(x_64);
lean_dec(x_64);
x_67 = lean_box(x_66);
x_68 = lean_apply_2(x_63, lean_box(0), x_67);
x_69 = lean_apply_4(x_61, lean_box(0), lean_box(0), x_68, x_65);
return x_69;
}
case 11:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_70 = lean_ctor_get(x_1, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_1, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_ctor_get(x_3, 2);
lean_inc(x_73);
lean_dec(x_3);
lean_inc(x_73);
lean_inc(x_72);
x_74 = lean_alloc_closure((void*)(l_Lean_hasAssignedMVar___redArg___lam__14___boxed), 5, 4);
lean_closure_set(x_74, 0, x_72);
lean_closure_set(x_74, 1, x_1);
lean_closure_set(x_74, 2, x_2);
lean_closure_set(x_74, 3, x_73);
x_75 = l_Lean_Expr_hasMVar(x_73);
lean_dec(x_73);
x_76 = lean_box(x_75);
x_77 = lean_apply_2(x_72, lean_box(0), x_76);
x_78 = lean_apply_4(x_70, lean_box(0), lean_box(0), x_77, x_74);
return x_78;
}
default: 
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_3);
lean_dec(x_2);
x_79 = lean_ctor_get(x_1, 0);
lean_inc(x_79);
lean_dec(x_1);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = lean_box(0);
x_82 = lean_apply_2(x_80, lean_box(0), x_81);
return x_82;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_hasAssignedMVar___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_hasAssignedMVar___redArg___lam__0(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_hasAssignedMVar___redArg___lam__1(x_1, x_2, x_3, x_4, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_hasAssignedMVar___redArg___lam__2(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_8);
lean_dec(x_8);
x_10 = l_Lean_hasAssignedMVar___redArg___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_hasAssignedMVar___redArg___lam__4(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_hasAssignedMVar___redArg___lam__5(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_hasAssignedMVar___redArg___lam__6(x_1, x_2, x_3, x_4, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_hasAssignedMVar___redArg___lam__7(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_hasAssignedMVar___redArg___lam__8(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_hasAssignedMVar___redArg___lam__9(x_1, x_2, x_3, x_4, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_hasAssignedMVar___redArg___lam__10(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_6);
lean_dec(x_6);
x_8 = l_Lean_hasAssignedMVar___redArg___lam__11(x_1, x_2, x_3, x_4, x_5, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_hasAssignedMVar___redArg___lam__12(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_hasAssignedMVar___redArg___lam__13(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignedMVar___redArg___lam__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_hasAssignedMVar___redArg___lam__14(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = l_Lean_hasAssignableLevelMVar___redArg(x_2, x_3, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = l_Lean_hasAssignableLevelMVar___redArg(x_2, x_3, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_hasAssignableLevelMVar___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_3);
lean_closure_set(x_7, 3, x_6);
lean_inc(x_4);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_hasAssignedLevelMVar___redArg___lam__1___boxed), 5, 4);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, x_4);
lean_closure_set(x_8, 3, x_7);
lean_inc(x_5);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_hasAssignableLevelMVar___redArg___lam__2___boxed), 5, 4);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_3);
lean_closure_set(x_9, 3, x_5);
x_10 = l_Lean_Level_hasMVar(x_5);
lean_dec(x_5);
x_11 = lean_box(x_10);
x_12 = lean_apply_2(x_1, lean_box(0), x_11);
lean_inc(x_4);
x_13 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_12, x_9);
x_14 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_13, x_8);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = l_Lean_hasAssignableLevelMVar___redArg(x_2, x_3, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
lean_inc(x_7);
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_hasAssignableLevelMVar___redArg___lam__3___boxed), 5, 4);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, x_2);
lean_closure_set(x_8, 3, x_7);
x_9 = l_Lean_Level_hasMVar(x_7);
lean_dec(x_7);
x_10 = lean_box(x_9);
x_11 = lean_apply_2(x_6, lean_box(0), x_10);
x_12 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_11, x_8);
return x_12;
}
case 2:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
lean_dec(x_3);
x_18 = l_Lean_hasAssignableLevelMVar___redArg___lam__1(x_15, x_1, x_2, x_13, x_16, x_17);
return x_18;
}
case 3:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_3, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_3, 1);
lean_inc(x_23);
lean_dec(x_3);
x_24 = l_Lean_hasAssignableLevelMVar___redArg___lam__1(x_21, x_1, x_2, x_19, x_22, x_23);
return x_24;
}
case 5:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_3, 0);
lean_inc(x_25);
lean_dec(x_3);
x_26 = l_Lean_isLevelMVarAssignable___redArg(x_1, x_2, x_25);
return x_26;
}
default: 
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_box(0);
x_30 = lean_apply_2(x_28, lean_box(0), x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_hasAssignableLevelMVar___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_hasAssignableLevelMVar___redArg___lam__0(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_hasAssignableLevelMVar___redArg___lam__2(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_hasAssignableLevelMVar___redArg___lam__3(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = l_Lean_hasAssignableMVar___redArg(x_2, x_3, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = l_Lean_hasAssignableMVar___redArg(x_2, x_3, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_hasAssignableMVar___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_3);
lean_closure_set(x_9, 3, x_7);
lean_inc(x_4);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_hasAssignedMVar___redArg___lam__1___boxed), 5, 4);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_1);
lean_closure_set(x_10, 2, x_4);
lean_closure_set(x_10, 3, x_9);
lean_inc(x_6);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_hasAssignableMVar___redArg___lam__2___boxed), 5, 4);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_6);
x_12 = l_Lean_Expr_hasMVar(x_6);
lean_dec(x_6);
x_13 = lean_box(x_12);
x_14 = lean_apply_2(x_1, lean_box(0), x_13);
lean_inc(x_4);
x_15 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_14, x_11);
x_16 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_15, x_10);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = l_Lean_hasAssignableMVar___redArg(x_2, x_3, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = l_Lean_hasAssignableMVar___redArg(x_2, x_3, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = l_Lean_hasAssignableMVar___redArg(x_2, x_3, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = l_Lean_hasAssignableMVar___redArg(x_2, x_3, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = l_Lean_hasAssignableMVar___redArg(x_2, x_3, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = l_Lean_hasAssignableMVar___redArg(x_2, x_3, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg___lam__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = l_Lean_hasAssignableMVar___redArg(x_2, x_3, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 2:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_MVarId_isAssignable___redArg(x_1, x_2, x_4);
return x_5;
}
case 3:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_Lean_hasAssignableLevelMVar___redArg(x_1, x_2, x_6);
return x_7;
}
case 4:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_hasAssignableLevelMVar), 4, 3);
lean_closure_set(x_9, 0, lean_box(0));
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_2);
x_10 = l_List_anyM___redArg(x_1, x_9, x_8);
return x_10;
}
case 5:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_dec(x_3);
lean_inc(x_15);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_13);
x_16 = lean_alloc_closure((void*)(l_Lean_hasAssignableMVar___redArg___lam__3___boxed), 5, 4);
lean_closure_set(x_16, 0, x_13);
lean_closure_set(x_16, 1, x_1);
lean_closure_set(x_16, 2, x_2);
lean_closure_set(x_16, 3, x_15);
lean_inc(x_11);
lean_inc(x_13);
x_17 = lean_alloc_closure((void*)(l_Lean_hasAssignedMVar___redArg___lam__6___boxed), 5, 4);
lean_closure_set(x_17, 0, x_15);
lean_closure_set(x_17, 1, x_13);
lean_closure_set(x_17, 2, x_11);
lean_closure_set(x_17, 3, x_16);
lean_inc(x_14);
lean_inc(x_13);
x_18 = lean_alloc_closure((void*)(l_Lean_hasAssignableMVar___redArg___lam__5___boxed), 5, 4);
lean_closure_set(x_18, 0, x_13);
lean_closure_set(x_18, 1, x_1);
lean_closure_set(x_18, 2, x_2);
lean_closure_set(x_18, 3, x_14);
x_19 = l_Lean_Expr_hasMVar(x_14);
lean_dec(x_14);
x_20 = lean_box(x_19);
x_21 = lean_apply_2(x_13, lean_box(0), x_20);
lean_inc(x_11);
x_22 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_21, x_18);
x_23 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_22, x_17);
return x_23;
}
case 6:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_ctor_get(x_3, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_3, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_3, 2);
lean_inc(x_29);
x_30 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_dec(x_3);
x_31 = l_Lean_hasAssignableMVar___redArg___lam__1(x_26, x_1, x_2, x_24, x_27, x_28, x_29, x_30);
lean_dec(x_27);
return x_31;
}
case 7:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_ctor_get(x_3, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_3, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_3, 2);
lean_inc(x_37);
x_38 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_dec(x_3);
x_39 = l_Lean_hasAssignableMVar___redArg___lam__1(x_34, x_1, x_2, x_32, x_35, x_36, x_37, x_38);
lean_dec(x_35);
return x_39;
}
case 8:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_40 = lean_ctor_get(x_1, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_1, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_ctor_get(x_3, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_3, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_3, 3);
lean_inc(x_45);
lean_dec(x_3);
lean_inc(x_45);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_42);
x_46 = lean_alloc_closure((void*)(l_Lean_hasAssignableMVar___redArg___lam__4___boxed), 5, 4);
lean_closure_set(x_46, 0, x_42);
lean_closure_set(x_46, 1, x_1);
lean_closure_set(x_46, 2, x_2);
lean_closure_set(x_46, 3, x_45);
lean_inc(x_40);
lean_inc(x_42);
x_47 = lean_alloc_closure((void*)(l_Lean_hasAssignedMVar___redArg___lam__9___boxed), 5, 4);
lean_closure_set(x_47, 0, x_45);
lean_closure_set(x_47, 1, x_42);
lean_closure_set(x_47, 2, x_40);
lean_closure_set(x_47, 3, x_46);
lean_inc(x_44);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_42);
x_48 = lean_alloc_closure((void*)(l_Lean_hasAssignableMVar___redArg___lam__7___boxed), 5, 4);
lean_closure_set(x_48, 0, x_42);
lean_closure_set(x_48, 1, x_1);
lean_closure_set(x_48, 2, x_2);
lean_closure_set(x_48, 3, x_44);
lean_inc(x_40);
lean_inc(x_42);
x_49 = lean_alloc_closure((void*)(l_Lean_hasAssignedMVar___redArg___lam__11___boxed), 6, 5);
lean_closure_set(x_49, 0, x_44);
lean_closure_set(x_49, 1, x_42);
lean_closure_set(x_49, 2, x_40);
lean_closure_set(x_49, 3, x_48);
lean_closure_set(x_49, 4, x_47);
lean_inc(x_43);
lean_inc(x_42);
x_50 = lean_alloc_closure((void*)(l_Lean_hasAssignableMVar___redArg___lam__8___boxed), 5, 4);
lean_closure_set(x_50, 0, x_42);
lean_closure_set(x_50, 1, x_1);
lean_closure_set(x_50, 2, x_2);
lean_closure_set(x_50, 3, x_43);
x_51 = l_Lean_Expr_hasMVar(x_43);
lean_dec(x_43);
x_52 = lean_box(x_51);
x_53 = lean_apply_2(x_42, lean_box(0), x_52);
lean_inc(x_40);
x_54 = lean_apply_4(x_40, lean_box(0), lean_box(0), x_53, x_50);
x_55 = lean_apply_4(x_40, lean_box(0), lean_box(0), x_54, x_49);
return x_55;
}
case 10:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_56 = lean_ctor_get(x_1, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_1, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_ctor_get(x_3, 1);
lean_inc(x_59);
lean_dec(x_3);
lean_inc(x_59);
lean_inc(x_58);
x_60 = lean_alloc_closure((void*)(l_Lean_hasAssignableMVar___redArg___lam__6___boxed), 5, 4);
lean_closure_set(x_60, 0, x_58);
lean_closure_set(x_60, 1, x_1);
lean_closure_set(x_60, 2, x_2);
lean_closure_set(x_60, 3, x_59);
x_61 = l_Lean_Expr_hasMVar(x_59);
lean_dec(x_59);
x_62 = lean_box(x_61);
x_63 = lean_apply_2(x_58, lean_box(0), x_62);
x_64 = lean_apply_4(x_56, lean_box(0), lean_box(0), x_63, x_60);
return x_64;
}
case 11:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_65 = lean_ctor_get(x_1, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_1, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_ctor_get(x_3, 2);
lean_inc(x_68);
lean_dec(x_3);
lean_inc(x_68);
lean_inc(x_67);
x_69 = lean_alloc_closure((void*)(l_Lean_hasAssignableMVar___redArg___lam__9___boxed), 5, 4);
lean_closure_set(x_69, 0, x_67);
lean_closure_set(x_69, 1, x_1);
lean_closure_set(x_69, 2, x_2);
lean_closure_set(x_69, 3, x_68);
x_70 = l_Lean_Expr_hasMVar(x_68);
lean_dec(x_68);
x_71 = lean_box(x_70);
x_72 = lean_apply_2(x_67, lean_box(0), x_71);
x_73 = lean_apply_4(x_65, lean_box(0), lean_box(0), x_72, x_69);
return x_73;
}
default: 
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_3);
lean_dec(x_2);
x_74 = lean_ctor_get(x_1, 0);
lean_inc(x_74);
lean_dec(x_1);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_76 = lean_box(0);
x_77 = lean_apply_2(x_75, lean_box(0), x_76);
return x_77;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_hasAssignableMVar___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_hasAssignableMVar___redArg___lam__0(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_hasAssignableMVar___redArg___lam__2(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_8);
lean_dec(x_8);
x_10 = l_Lean_hasAssignableMVar___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_hasAssignableMVar___redArg___lam__3(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_hasAssignableMVar___redArg___lam__5(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_hasAssignableMVar___redArg___lam__4(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_hasAssignableMVar___redArg___lam__7(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg___lam__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_hasAssignableMVar___redArg___lam__8(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_hasAssignableMVar___redArg___lam__6(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___redArg___lam__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_hasAssignableMVar___redArg___lam__9(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 4);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 5);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 6);
lean_inc(x_12);
x_13 = l_Lean_PersistentHashMap_insert___redArg(x_1, x_2, x_12, x_3, x_4);
x_14 = lean_ctor_get(x_5, 7);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 8);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_7);
lean_ctor_set(x_16, 2, x_8);
lean_ctor_set(x_16, 3, x_9);
lean_ctor_set(x_16, 4, x_10);
lean_ctor_set(x_16, 5, x_11);
lean_ctor_set(x_16, 6, x_13);
lean_ctor_set(x_16, 7, x_14);
lean_ctor_set(x_16, 8, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lean_instBEqLevelMVarId;
x_5 = lean_alloc_closure((void*)(l___private_Lean_Level_0__Lean_hashLevelMVarId____x40_Lean_Level___hyg_522____boxed), 1, 0);
x_6 = lean_alloc_closure((void*)(l_Lean_assignLevelMVar___redArg___lam__0), 5, 4);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
lean_closure_set(x_6, 2, x_2);
lean_closure_set(x_6, 3, x_3);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_1(x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_assignLevelMVar___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_assignLevelMVarExp_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; size_t x_7; lean_object* x_8; size_t x_9; lean_object* x_10; 
x_4 = l_Lean_instBEqLevelMVarId;
x_5 = lean_alloc_closure((void*)(l___private_Lean_Level_0__Lean_hashLevelMVarId____x40_Lean_Level___hyg_522____boxed), 1, 0);
x_6 = l___private_Lean_Level_0__Lean_hashLevelMVarId____x40_Lean_Level___hyg_522_(x_2);
x_7 = lean_uint64_to_usize(x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert_spec__0___redArg(x_4, x_5, x_1, x_7, x_9, x_2, x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_assignLevelMVarExp_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___Lean_assignLevelMVarExp_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lean_assign_lmvar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 5);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 6);
lean_inc(x_10);
x_11 = l_Lean_PersistentHashMap_insert___at___Lean_assignLevelMVarExp_spec__0___redArg(x_10, x_2, x_3);
x_12 = lean_ctor_get(x_1, 7);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 8);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 2, x_6);
lean_ctor_set(x_14, 3, x_7);
lean_ctor_set(x_14, 4, x_8);
lean_ctor_set(x_14, 5, x_9);
lean_ctor_set(x_14, 6, x_11);
lean_ctor_set(x_14, 7, x_12);
lean_ctor_set(x_14, 8, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 4);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 5);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 6);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 7);
lean_inc(x_13);
x_14 = l_Lean_PersistentHashMap_insert___redArg(x_1, x_2, x_13, x_3, x_4);
x_15 = lean_ctor_get(x_5, 8);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_7);
lean_ctor_set(x_16, 2, x_8);
lean_ctor_set(x_16, 3, x_9);
lean_ctor_set(x_16, 4, x_10);
lean_ctor_set(x_16, 5, x_11);
lean_ctor_set(x_16, 6, x_12);
lean_ctor_set(x_16, 7, x_14);
lean_ctor_set(x_16, 8, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lean_instBEqMVarId;
x_5 = l_Lean_instHashableMVarId;
x_6 = lean_alloc_closure((void*)(l_Lean_MVarId_assign___redArg___lam__0), 5, 4);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
lean_closure_set(x_6, 2, x_2);
lean_closure_set(x_6, 3, x_3);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_1(x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MVarId_assign___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_assignExp_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; size_t x_7; lean_object* x_8; size_t x_9; lean_object* x_10; 
x_4 = l_Lean_instBEqMVarId;
x_5 = l_Lean_instHashableMVarId;
x_6 = l___private_Lean_Expr_0__Lean_hashMVarId____x40_Lean_Expr___hyg_1984_(x_2);
x_7 = lean_uint64_to_usize(x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert_spec__0___redArg(x_4, x_5, x_1, x_7, x_9, x_2, x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_assignExp_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___Lean_assignExp_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lean_assign_mvar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 5);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 6);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 7);
lean_inc(x_11);
x_12 = l_Lean_PersistentHashMap_insert___at___Lean_assignExp_spec__0___redArg(x_11, x_2, x_3);
x_13 = lean_ctor_get(x_1, 8);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 2, x_6);
lean_ctor_set(x_14, 3, x_7);
lean_ctor_set(x_14, 4, x_8);
lean_ctor_set(x_14, 5, x_9);
lean_ctor_set(x_14, 6, x_10);
lean_ctor_set(x_14, 7, x_12);
lean_ctor_set(x_14, 8, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
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
lean_dec(x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
x_17 = l_Lean_PersistentHashMap_insert___redArg(x_3, x_4, x_15, x_5, x_16);
x_18 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_8);
lean_ctor_set(x_18, 2, x_9);
lean_ctor_set(x_18, 3, x_10);
lean_ctor_set(x_18, 4, x_11);
lean_ctor_set(x_18, 5, x_12);
lean_ctor_set(x_18, 6, x_13);
lean_ctor_set(x_18, 7, x_14);
lean_ctor_set(x_18, 8, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l_Lean_instBEqMVarId;
x_6 = l_Lean_instHashableMVarId;
x_7 = lean_alloc_closure((void*)(l_Lean_assignDelayedMVar___redArg___lam__0), 6, 5);
lean_closure_set(x_7, 0, x_3);
lean_closure_set(x_7, 1, x_4);
lean_closure_set(x_7, 2, x_5);
lean_closure_set(x_7, 3, x_6);
lean_closure_set(x_7, 4, x_2);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_1(x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_assignDelayedMVar___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVarsImp___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_instantiate_level_mvars(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_instantiate_level_mvars(x_5, x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_closure((void*)(l_Lean_instantiateLevelMVars___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_instantiateLevelMVars___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_10, 0, x_7);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_apply_1(x_11, x_10);
x_13 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_12, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
lean_inc(x_4);
x_8 = lean_alloc_closure((void*)(l_Lean_instantiateLevelMVars___redArg___lam__2), 5, 4);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_7);
lean_closure_set(x_8, 2, x_2);
lean_closure_set(x_8, 3, x_4);
x_9 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_instantiateLevelMVars___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateLevelMVars___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instantiateLevelMVars___redArg___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVarsImp___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_instantiate_expr_mvars(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_instantiate_expr_mvars(x_5, x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_closure((void*)(l_Lean_instantiateExprMVars___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_instantiateLevelMVars___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_10, 0, x_7);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_apply_1(x_11, x_10);
x_13 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_12, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
lean_inc(x_4);
x_8 = lean_alloc_closure((void*)(l_Lean_instantiateExprMVars___redArg___lam__2), 5, 4);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_7);
lean_closure_set(x_8, 2, x_2);
lean_closure_set(x_8, 3, x_4);
x_9 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_instantiateExprMVars___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateExprMVars___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadMCtxStateRefT_x27MetavarContextST(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_instMonadLiftT(lean_box(0));
lean_inc(x_2);
x_3 = l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg(x_2);
x_4 = l_instMonadStateOfMonadStateOf___redArg(x_3);
x_5 = lean_alloc_closure((void*)(l_StateRefT_x27_get), 5, 4);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, lean_box(0));
lean_closure_set(x_5, 2, lean_box(0));
lean_closure_set(x_5, 3, x_2);
x_6 = lean_alloc_closure((void*)(l_modify), 4, 3);
lean_closure_set(x_6, 0, lean_box(0));
lean_closure_set(x_6, 1, lean_box(0));
lean_closure_set(x_6, 2, x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVarsCore___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_unsigned_to_nat(8u);
x_6 = lean_unsigned_to_nat(2u);
x_7 = lean_nat_shiftl(x_5, x_6);
x_8 = lean_unsigned_to_nat(3u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = lean_st_mk_ref(x_1, x_4);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = l_Nat_nextPowerOfTwo(x_9);
lean_dec(x_9);
x_15 = lean_box(0);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_mk_array(x_14, x_15);
lean_ctor_set(x_10, 1, x_17);
lean_ctor_set(x_10, 0, x_16);
x_18 = lean_st_mk_ref(x_10, x_13);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = l_instMonadEST(lean_box(0), lean_box(0));
x_23 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_22);
x_24 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_23);
x_25 = l_StateRefT_x27_instMonadLift(lean_box(0), lean_box(0), lean_box(0));
x_26 = l_Lean_instMonadMCtxStateRefT_x27MetavarContextST(lean_box(0));
x_27 = lean_alloc_closure((void*)(l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_27, 0, x_26);
lean_closure_set(x_27, 1, x_25);
x_28 = l_instMonadLiftT(lean_box(0));
x_29 = lean_alloc_closure((void*)(l_StateRefT_x27_get), 5, 4);
lean_closure_set(x_29, 0, lean_box(0));
lean_closure_set(x_29, 1, lean_box(0));
lean_closure_set(x_29, 2, lean_box(0));
lean_closure_set(x_29, 3, x_28);
x_30 = l_StateRefT_x27_instMonadLift(lean_box(0), lean_box(0), lean_box(0));
x_31 = lean_apply_2(x_30, lean_box(0), x_29);
lean_ctor_set(x_18, 1, x_27);
lean_ctor_set(x_18, 0, x_31);
x_32 = l_Lean_instantiateExprMVars___redArg(x_24, x_18, x_2);
lean_inc(x_12);
lean_inc(x_20);
x_33 = lean_apply_3(x_32, x_20, x_12, x_21);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_st_ref_get(x_20, x_35);
lean_dec(x_20);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_36, 1);
x_39 = lean_ctor_get(x_36, 0);
lean_dec(x_39);
x_40 = lean_st_ref_get(x_12, x_38);
lean_dec(x_12);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_ctor_set(x_36, 1, x_42);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_40, 0, x_36);
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
lean_ctor_set(x_36, 1, x_43);
lean_ctor_set(x_36, 0, x_34);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_36);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_46 = lean_ctor_get(x_36, 1);
lean_inc(x_46);
lean_dec(x_36);
x_47 = lean_st_ref_get(x_12, x_46);
lean_dec(x_12);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_34);
lean_ctor_set(x_51, 1, x_48);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_53 = lean_ctor_get(x_18, 0);
x_54 = lean_ctor_get(x_18, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_18);
x_55 = l_instMonadEST(lean_box(0), lean_box(0));
x_56 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_55);
x_57 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_56);
x_58 = l_StateRefT_x27_instMonadLift(lean_box(0), lean_box(0), lean_box(0));
x_59 = l_Lean_instMonadMCtxStateRefT_x27MetavarContextST(lean_box(0));
x_60 = lean_alloc_closure((void*)(l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_60, 0, x_59);
lean_closure_set(x_60, 1, x_58);
x_61 = l_instMonadLiftT(lean_box(0));
x_62 = lean_alloc_closure((void*)(l_StateRefT_x27_get), 5, 4);
lean_closure_set(x_62, 0, lean_box(0));
lean_closure_set(x_62, 1, lean_box(0));
lean_closure_set(x_62, 2, lean_box(0));
lean_closure_set(x_62, 3, x_61);
x_63 = l_StateRefT_x27_instMonadLift(lean_box(0), lean_box(0), lean_box(0));
x_64 = lean_apply_2(x_63, lean_box(0), x_62);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_60);
x_66 = l_Lean_instantiateExprMVars___redArg(x_57, x_65, x_2);
lean_inc(x_12);
lean_inc(x_53);
x_67 = lean_apply_3(x_66, x_53, x_12, x_54);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_st_ref_get(x_53, x_69);
lean_dec(x_53);
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
x_73 = lean_st_ref_get(x_12, x_71);
lean_dec(x_12);
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
if (lean_is_scalar(x_72)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_72;
}
lean_ctor_set(x_77, 0, x_68);
lean_ctor_set(x_77, 1, x_74);
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
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_79 = lean_ctor_get(x_10, 0);
x_80 = lean_ctor_get(x_10, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_10);
x_81 = l_Nat_nextPowerOfTwo(x_9);
lean_dec(x_9);
x_82 = lean_box(0);
x_83 = lean_unsigned_to_nat(0u);
x_84 = lean_mk_array(x_81, x_82);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_st_mk_ref(x_85, x_80);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_89 = x_86;
} else {
 lean_dec_ref(x_86);
 x_89 = lean_box(0);
}
x_90 = l_instMonadEST(lean_box(0), lean_box(0));
x_91 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_90);
x_92 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_91);
x_93 = l_StateRefT_x27_instMonadLift(lean_box(0), lean_box(0), lean_box(0));
x_94 = l_Lean_instMonadMCtxStateRefT_x27MetavarContextST(lean_box(0));
x_95 = lean_alloc_closure((void*)(l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_95, 0, x_94);
lean_closure_set(x_95, 1, x_93);
x_96 = l_instMonadLiftT(lean_box(0));
x_97 = lean_alloc_closure((void*)(l_StateRefT_x27_get), 5, 4);
lean_closure_set(x_97, 0, lean_box(0));
lean_closure_set(x_97, 1, lean_box(0));
lean_closure_set(x_97, 2, lean_box(0));
lean_closure_set(x_97, 3, x_96);
x_98 = l_StateRefT_x27_instMonadLift(lean_box(0), lean_box(0), lean_box(0));
x_99 = lean_apply_2(x_98, lean_box(0), x_97);
if (lean_is_scalar(x_89)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_89;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_95);
x_101 = l_Lean_instantiateExprMVars___redArg(x_92, x_100, x_2);
lean_inc(x_79);
lean_inc(x_87);
x_102 = lean_apply_3(x_101, x_87, x_79, x_88);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_st_ref_get(x_87, x_104);
lean_dec(x_87);
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_107 = x_105;
} else {
 lean_dec_ref(x_105);
 x_107 = lean_box(0);
}
x_108 = lean_st_ref_get(x_79, x_106);
lean_dec(x_79);
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
if (lean_is_scalar(x_107)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_107;
}
lean_ctor_set(x_112, 0, x_103);
lean_ctor_set(x_112, 1, x_109);
if (lean_is_scalar(x_111)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_111;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_110);
return x_113;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVarsCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_instantiateMVarsCore___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = l_runST___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_apply_2(x_5, lean_box(0), x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = l_Lean_instantiateMVarsCore(x_5, x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_closure((void*)(l_Lean_instantiateMVars___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_instantiateMVars___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_7);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_apply_1(x_11, x_9);
x_13 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_12, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_apply_2(x_6, lean_box(0), x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_8);
lean_inc(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_instantiateMVars___redArg___lam__2), 5, 4);
lean_closure_set(x_9, 0, x_3);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_2);
lean_closure_set(x_9, 3, x_8);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_10, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_instantiateMVars___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instantiateMVars___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___redArg___lam__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_instantiateLCtxMVars___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Name_quickCmp(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_instantiateLCtxMVars___redArg___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_3);
x_10 = l_Lean_RBNode_find(lean_box(0), x_1, lean_box(0), x_2, x_3);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_11 = lean_mk_string_unchecked("Lean.MetavarContext", 19, 19);
x_12 = lean_mk_string_unchecked("Lean.instantiateLCtxMVars", 25, 25);
x_13 = lean_unsigned_to_nat(597u);
x_14 = lean_unsigned_to_nat(12u);
x_15 = lean_mk_string_unchecked("Invalid auxiliary declaration found in local context: ", 54, 54);
x_16 = lean_box(1);
x_17 = lean_unbox(x_16);
x_18 = l_Lean_Name_toString(x_4, x_17, x_5);
x_19 = lean_string_append(x_15, x_18);
lean_dec(x_18);
x_20 = lean_mk_string_unchecked(" does not have an associated full name.", 39, 39);
x_21 = lean_string_append(x_19, x_20);
lean_dec(x_20);
x_22 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_11, x_12, x_13, x_14, x_21);
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_11);
x_23 = l_panic___redArg(x_6, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_6);
lean_dec(x_5);
x_24 = lean_ctor_get(x_10, 0);
lean_inc(x_24);
lean_dec(x_10);
x_25 = l_Lean_LocalContext_mkAuxDecl(x_7, x_3, x_4, x_9, x_24);
x_26 = lean_apply_2(x_8, lean_box(0), x_25);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_LocalContext_mkLocalDecl(x_1, x_2, x_3, x_7, x_4, x_5);
x_9 = lean_apply_2(x_6, lean_box(0), x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_LocalContext_mkLetDecl(x_1, x_2, x_3, x_4, x_8, x_5, x_6);
x_10 = lean_apply_2(x_7, lean_box(0), x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_box(x_4);
x_13 = lean_box(x_5);
x_14 = lean_alloc_closure((void*)(l_Lean_instantiateLCtxMVars___redArg___lam__4___boxed), 8, 7);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_3);
lean_closure_set(x_14, 3, x_11);
lean_closure_set(x_14, 4, x_12);
lean_closure_set(x_14, 5, x_13);
lean_closure_set(x_14, 6, x_6);
x_15 = l_Lean_instantiateMVars___redArg(x_7, x_8, x_9);
x_16 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_15, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___redArg___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*4 + 1);
x_12 = lean_box(x_11);
if (lean_obj_tag(x_12) == 2)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_10, 3);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_alloc_closure((void*)(l_Lean_instantiateLCtxMVars___redArg___lam__2), 9, 8);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_13);
lean_closure_set(x_16, 3, x_14);
lean_closure_set(x_16, 4, x_3);
lean_closure_set(x_16, 5, x_4);
lean_closure_set(x_16, 6, x_9);
lean_closure_set(x_16, 7, x_5);
x_17 = l_Lean_instantiateMVars___redArg(x_6, x_7, x_15);
x_18 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_17, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_10, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_10, 3);
lean_inc(x_21);
x_22 = lean_ctor_get_uint8(x_10, sizeof(void*)*4);
lean_dec(x_10);
x_23 = lean_box(x_22);
x_24 = lean_box(x_11);
x_25 = lean_alloc_closure((void*)(l_Lean_instantiateLCtxMVars___redArg___lam__3___boxed), 7, 6);
lean_closure_set(x_25, 0, x_9);
lean_closure_set(x_25, 1, x_19);
lean_closure_set(x_25, 2, x_20);
lean_closure_set(x_25, 3, x_23);
lean_closure_set(x_25, 4, x_24);
lean_closure_set(x_25, 5, x_5);
x_26 = l_Lean_instantiateMVars___redArg(x_6, x_7, x_21);
x_27 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_26, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_10, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_10, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_10, 4);
lean_inc(x_31);
x_32 = lean_ctor_get_uint8(x_10, sizeof(void*)*5);
x_33 = lean_ctor_get_uint8(x_10, sizeof(void*)*5 + 1);
lean_dec(x_10);
x_34 = lean_box(x_32);
x_35 = lean_box(x_33);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_36 = lean_alloc_closure((void*)(l_Lean_instantiateLCtxMVars___redArg___lam__5___boxed), 11, 10);
lean_closure_set(x_36, 0, x_9);
lean_closure_set(x_36, 1, x_28);
lean_closure_set(x_36, 2, x_29);
lean_closure_set(x_36, 3, x_34);
lean_closure_set(x_36, 4, x_35);
lean_closure_set(x_36, 5, x_5);
lean_closure_set(x_36, 6, x_6);
lean_closure_set(x_36, 7, x_7);
lean_closure_set(x_36, 8, x_31);
lean_closure_set(x_36, 9, x_8);
x_37 = l_Lean_instantiateMVars___redArg(x_6, x_7, x_30);
x_38 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_37, x_36);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; lean_object* x_18; lean_object* x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_4 = lean_alloc_closure((void*)(l_Lean_instantiateLCtxMVars___redArg___lam__0___boxed), 2, 0);
x_5 = lean_alloc_closure((void*)(l_Lean_instantiateLCtxMVars___redArg___lam__1___boxed), 1, 0);
x_6 = l_Lean_instInhabitedLocalContext;
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_1);
x_11 = l_instInhabitedOfMonad___redArg(x_1, x_6);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_instantiateLCtxMVars___redArg___lam__6), 10, 8);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_7);
lean_closure_set(x_12, 2, x_5);
lean_closure_set(x_12, 3, x_11);
lean_closure_set(x_12, 4, x_10);
lean_closure_set(x_12, 5, x_1);
lean_closure_set(x_12, 6, x_2);
lean_closure_set(x_12, 7, x_8);
x_13 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_unsigned_to_nat(5u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_to_nat(x_17);
x_19 = lean_nat_pow(x_15, x_18);
lean_dec(x_18);
x_20 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_21 = lean_usize_to_nat(x_20);
x_22 = lean_mk_empty_array_with_capacity(x_21);
lean_dec(x_21);
lean_inc(x_22);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_25, 2, x_24);
lean_ctor_set(x_25, 3, x_24);
lean_ctor_set_usize(x_25, 4, x_17);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_27, 2, x_26);
x_28 = l_Lean_LocalContext_foldlM___redArg(x_1, x_3, x_12, x_27, x_24);
return x_28;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_instantiateLCtxMVars___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_instantiateLCtxMVars___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___redArg___lam__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_instantiateLCtxMVars___redArg___lam__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l_Lean_instantiateLCtxMVars___redArg___lam__3(x_1, x_2, x_3, x_8, x_9, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = lean_unbox(x_6);
lean_dec(x_6);
x_11 = l_Lean_instantiateLCtxMVars___redArg___lam__4(x_1, x_2, x_3, x_4, x_9, x_10, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___redArg___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l_Lean_instantiateLCtxMVars___redArg___lam__5(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVarDeclMVars___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 4);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 3);
x_15 = lean_ctor_get(x_1, 4);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
x_17 = lean_ctor_get(x_1, 5);
x_18 = lean_ctor_get(x_1, 6);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_19 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_2);
lean_ctor_set(x_19, 2, x_3);
lean_ctor_set(x_19, 3, x_14);
lean_ctor_set(x_19, 4, x_15);
lean_ctor_set(x_19, 5, x_17);
lean_ctor_set(x_19, 6, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*7, x_16);
x_20 = l_Lean_PersistentHashMap_insert___redArg(x_4, x_5, x_12, x_6, x_19);
x_21 = lean_ctor_get(x_7, 5);
lean_inc(x_21);
x_22 = lean_ctor_get(x_7, 6);
lean_inc(x_22);
x_23 = lean_ctor_get(x_7, 7);
lean_inc(x_23);
x_24 = lean_ctor_get(x_7, 8);
lean_inc(x_24);
lean_dec(x_7);
x_25 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_25, 0, x_8);
lean_ctor_set(x_25, 1, x_9);
lean_ctor_set(x_25, 2, x_10);
lean_ctor_set(x_25, 3, x_11);
lean_ctor_set(x_25, 4, x_20);
lean_ctor_set(x_25, 5, x_21);
lean_ctor_set(x_25, 6, x_22);
lean_ctor_set(x_25, 7, x_23);
lean_ctor_set(x_25, 8, x_24);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVarDeclMVars___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_sharecommon_quick(x_8);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_closure((void*)(l_Lean_instantiateMVarDeclMVars___redArg___lam__0___boxed), 7, 6);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_10);
lean_closure_set(x_12, 2, x_11);
lean_closure_set(x_12, 3, x_3);
lean_closure_set(x_12, 4, x_4);
lean_closure_set(x_12, 5, x_5);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_apply_1(x_13, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVarDeclMVars___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_5);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_instantiateMVarDeclMVars___redArg___lam__1), 7, 6);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_2);
lean_closure_set(x_9, 3, x_3);
lean_closure_set(x_9, 4, x_4);
lean_closure_set(x_9, 5, x_5);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lean_instantiateMVars___redArg(x_6, x_5, x_10);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_11, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVarDeclMVars___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_Lean_MetavarContext_getDecl(x_7, x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l_Lean_instantiateMVarDeclMVars___redArg___lam__2), 8, 7);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_3);
lean_closure_set(x_9, 3, x_1);
lean_closure_set(x_9, 4, x_4);
lean_closure_set(x_9, 5, x_5);
lean_closure_set(x_9, 6, x_6);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_instantiateLCtxMVars___redArg(x_5, x_4, x_10);
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_11, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVarDeclMVars___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = l_Lean_instBEqMVarId;
x_5 = l_Lean_instHashableMVarId;
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_6);
lean_inc(x_2);
x_7 = lean_alloc_closure((void*)(l_Lean_instantiateMVarDeclMVars___redArg___lam__3), 7, 6);
lean_closure_set(x_7, 0, x_3);
lean_closure_set(x_7, 1, x_4);
lean_closure_set(x_7, 2, x_5);
lean_closure_set(x_7, 3, x_2);
lean_closure_set(x_7, 4, x_1);
lean_closure_set(x_7, 5, x_6);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVarDeclMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_instantiateMVarDeclMVars___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVarDeclMVars___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_instantiateMVarDeclMVars___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set(x_8, 3, x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*4, x_4);
lean_ctor_set_uint8(x_8, sizeof(void*)*4 + 1, x_5);
x_9 = lean_apply_2(x_6, lean_box(0), x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_2);
lean_ctor_set(x_9, 2, x_3);
lean_ctor_set(x_9, 3, x_4);
lean_ctor_set(x_9, 4, x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*5, x_5);
lean_ctor_set_uint8(x_9, sizeof(void*)*5 + 1, x_6);
x_10 = lean_apply_2(x_7, lean_box(0), x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_box(x_4);
x_13 = lean_box(x_5);
x_14 = lean_alloc_closure((void*)(l_Lean_instantiateLocalDeclMVars___redArg___lam__1___boxed), 8, 7);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_3);
lean_closure_set(x_14, 3, x_11);
lean_closure_set(x_14, 4, x_12);
lean_closure_set(x_14, 5, x_13);
lean_closure_set(x_14, 6, x_6);
x_15 = l_Lean_instantiateMVars___redArg(x_7, x_8, x_9);
x_16 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_15, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 3);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_3, sizeof(void*)*4);
x_12 = lean_ctor_get_uint8(x_3, sizeof(void*)*4 + 1);
lean_dec(x_3);
x_13 = lean_box(x_11);
x_14 = lean_box(x_12);
x_15 = lean_alloc_closure((void*)(l_Lean_instantiateLocalDeclMVars___redArg___lam__0___boxed), 7, 6);
lean_closure_set(x_15, 0, x_7);
lean_closure_set(x_15, 1, x_8);
lean_closure_set(x_15, 2, x_9);
lean_closure_set(x_15, 3, x_13);
lean_closure_set(x_15, 4, x_14);
lean_closure_set(x_15, 5, x_6);
x_16 = l_Lean_instantiateMVars___redArg(x_1, x_2, x_10);
x_17 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_16, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_3, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_3, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_3, 3);
lean_inc(x_24);
x_25 = lean_ctor_get(x_3, 4);
lean_inc(x_25);
x_26 = lean_ctor_get_uint8(x_3, sizeof(void*)*5);
x_27 = lean_ctor_get_uint8(x_3, sizeof(void*)*5 + 1);
lean_dec(x_3);
x_28 = lean_box(x_26);
x_29 = lean_box(x_27);
lean_inc(x_18);
lean_inc(x_2);
lean_inc(x_1);
x_30 = lean_alloc_closure((void*)(l_Lean_instantiateLocalDeclMVars___redArg___lam__2___boxed), 11, 10);
lean_closure_set(x_30, 0, x_21);
lean_closure_set(x_30, 1, x_22);
lean_closure_set(x_30, 2, x_23);
lean_closure_set(x_30, 3, x_28);
lean_closure_set(x_30, 4, x_29);
lean_closure_set(x_30, 5, x_20);
lean_closure_set(x_30, 6, x_1);
lean_closure_set(x_30, 7, x_2);
lean_closure_set(x_30, 8, x_25);
lean_closure_set(x_30, 9, x_18);
x_31 = l_Lean_instantiateMVars___redArg(x_1, x_2, x_24);
x_32 = lean_apply_4(x_18, lean_box(0), lean_box(0), x_31, x_30);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_instantiateLocalDeclMVars___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l_Lean_instantiateLocalDeclMVars___redArg___lam__0(x_1, x_2, x_3, x_8, x_9, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = lean_unbox(x_6);
lean_dec(x_6);
x_11 = l_Lean_instantiateLocalDeclMVars___redArg___lam__1(x_1, x_2, x_3, x_4, x_9, x_10, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l_Lean_instantiateLocalDeclMVars___redArg___lam__2(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_DependsOn_instMonadMCtxM___lam__0(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_DependsOn_instMonadMCtxM___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_box(0);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_apply_1(x_1, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_DependsOn_instMonadMCtxM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_1 = lean_alloc_closure((void*)(l_Lean_DependsOn_instMonadMCtxM___lam__0___boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_DependsOn_instMonadMCtxM___lam__1), 2, 0);
x_3 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_4 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_5 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_6 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_7 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_8 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_9 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_4);
x_11 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 2, x_6);
lean_ctor_set(x_11, 3, x_7);
lean_ctor_set(x_11, 4, x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
lean_inc(x_12);
x_13 = lean_alloc_closure((void*)(l_StateT_get), 4, 3);
lean_closure_set(x_13, 0, lean_box(0));
lean_closure_set(x_13, 1, lean_box(0));
lean_closure_set(x_13, 2, x_12);
x_14 = lean_alloc_closure((void*)(l_StateT_bind), 8, 7);
lean_closure_set(x_14, 0, lean_box(0));
lean_closure_set(x_14, 1, lean_box(0));
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, lean_box(0));
lean_closure_set(x_14, 4, lean_box(0));
lean_closure_set(x_14, 5, x_13);
lean_closure_set(x_14, 6, x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_DependsOn_instMonadMCtxM___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_DependsOn_instMonadMCtxM___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_expr_eqv(x_5, x_1);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_Expr_hash(x_4);
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
x_29 = l_Lean_Expr_hash(x_25);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__1_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__1_spec__1_spec__1___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__1___redArg(lean_object* x_1) {
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
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__1_spec__1___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; uint8_t x_10; uint8_t x_75; 
x_75 = l_Lean_Expr_hasMVar(x_1);
if (x_75 == 0)
{
uint8_t x_76; 
x_76 = l_Lean_Expr_hasFVar(x_1);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_1);
x_77 = lean_box(x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_2);
return x_78;
}
else
{
x_10 = x_75;
goto block_74;
}
}
else
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_box(0);
x_80 = lean_unbox(x_79);
x_10 = x_80;
goto block_74;
}
block_9:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_box(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
block_74:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint64_t x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; lean_object* x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; size_t x_23; size_t x_24; lean_object* x_25; size_t x_26; size_t x_27; size_t x_28; lean_object* x_29; uint8_t x_30; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = lean_array_get_size(x_12);
x_14 = l_Lean_Expr_hash(x_1);
x_15 = lean_unsigned_to_nat(32u);
x_16 = lean_uint64_of_nat(x_15);
x_17 = lean_uint64_shift_right(x_14, x_16);
x_18 = lean_uint64_xor(x_14, x_17);
x_19 = lean_unsigned_to_nat(16u);
x_20 = lean_uint64_of_nat(x_19);
x_21 = lean_uint64_shift_right(x_18, x_20);
x_22 = lean_uint64_xor(x_18, x_21);
x_23 = lean_uint64_to_usize(x_22);
x_24 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_usize_of_nat(x_25);
x_27 = lean_usize_sub(x_24, x_26);
x_28 = lean_usize_land(x_23, x_27);
x_29 = lean_array_uget(x_12, x_28);
lean_dec(x_12);
x_30 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__0___redArg(x_1, x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; uint8_t x_39; 
x_31 = lean_ctor_get(x_11, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_11, 1);
lean_inc(x_32);
x_33 = lean_box(1);
x_34 = lean_array_get_size(x_32);
x_35 = lean_usize_of_nat(x_34);
lean_dec(x_34);
x_36 = lean_usize_sub(x_35, x_26);
x_37 = lean_usize_land(x_23, x_36);
x_38 = lean_array_uget(x_32, x_37);
x_39 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__0___redArg(x_1, x_38);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_11);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_41 = lean_ctor_get(x_11, 1);
lean_dec(x_41);
x_42 = lean_ctor_get(x_11, 0);
lean_dec(x_42);
x_43 = lean_box(0);
x_44 = lean_nat_add(x_31, x_25);
lean_dec(x_31);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set(x_45, 2, x_38);
x_46 = lean_array_uset(x_32, x_37, x_45);
x_47 = lean_unsigned_to_nat(2u);
x_48 = lean_nat_shiftl(x_44, x_47);
x_49 = lean_unsigned_to_nat(3u);
x_50 = lean_nat_div(x_48, x_49);
lean_dec(x_48);
x_51 = lean_array_get_size(x_46);
x_52 = lean_nat_dec_le(x_50, x_51);
lean_dec(x_51);
lean_dec(x_50);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__1___redArg(x_46);
lean_ctor_set(x_11, 1, x_53);
lean_ctor_set(x_11, 0, x_44);
x_54 = lean_unbox(x_33);
x_3 = x_54;
x_4 = x_11;
goto block_9;
}
else
{
uint8_t x_55; 
lean_ctor_set(x_11, 1, x_46);
lean_ctor_set(x_11, 0, x_44);
x_55 = lean_unbox(x_33);
x_3 = x_55;
x_4 = x_11;
goto block_9;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec(x_11);
x_56 = lean_box(0);
x_57 = lean_nat_add(x_31, x_25);
lean_dec(x_31);
x_58 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_58, 0, x_1);
lean_ctor_set(x_58, 1, x_56);
lean_ctor_set(x_58, 2, x_38);
x_59 = lean_array_uset(x_32, x_37, x_58);
x_60 = lean_unsigned_to_nat(2u);
x_61 = lean_nat_shiftl(x_57, x_60);
x_62 = lean_unsigned_to_nat(3u);
x_63 = lean_nat_div(x_61, x_62);
lean_dec(x_61);
x_64 = lean_array_get_size(x_59);
x_65 = lean_nat_dec_le(x_63, x_64);
lean_dec(x_64);
lean_dec(x_63);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__1___redArg(x_59);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_57);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_unbox(x_33);
x_3 = x_68;
x_4 = x_67;
goto block_9;
}
else
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_57);
lean_ctor_set(x_69, 1, x_59);
x_70 = lean_unbox(x_33);
x_3 = x_70;
x_4 = x_69;
goto block_9;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_1);
x_71 = lean_unbox(x_33);
x_3 = x_71;
x_4 = x_11;
goto block_9;
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_11);
lean_dec(x_1);
x_72 = lean_box(x_10);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_2);
return x_73;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_3);
x_5 = l___private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain(x_1, x_2, x_3, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at_____private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = l_Lean_MetavarContext_getExprAssignmentCore_x3f(x_3, x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain_spec__1_spec__1_spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_uget(x_3, x_4);
lean_inc(x_2);
x_8 = l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain_spec__1_spec__1(x_1, x_2, x_7);
lean_dec(x_7);
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
lean_dec(x_2);
return x_8;
}
}
else
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
return x_14;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain_spec__1_spec__1_spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_15; lean_object* x_19; 
x_7 = lean_box(1);
x_19 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_19) == 0)
{
x_8 = x_1;
goto block_14;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_15 = x_21;
goto block_18;
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
lean_dec(x_2);
x_13 = lean_unbox(x_7);
return x_13;
}
}
block_18:
{
lean_object* x_16; uint8_t x_17; 
lean_inc(x_2);
x_16 = lean_apply_1(x_2, x_15);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
x_8 = x_17;
goto block_14;
}
}
else
{
lean_object* x_22; uint8_t x_23; 
lean_dec(x_2);
x_22 = lean_box(0);
x_23 = lean_unbox(x_22);
return x_23;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain_spec__1_spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get_size(x_4);
x_7 = lean_nat_dec_lt(x_5, x_6);
if (x_7 == 0)
{
lean_dec(x_6);
lean_dec(x_2);
return x_7;
}
else
{
if (x_7 == 0)
{
lean_dec(x_6);
lean_dec(x_2);
return x_7;
}
else
{
size_t x_8; size_t x_9; uint8_t x_10; 
x_8 = lean_usize_of_nat(x_5);
x_9 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_10 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain_spec__1_spec__1_spec__1(x_1, x_2, x_4, x_8, x_9);
return x_10;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_11);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_dec(x_13);
lean_dec(x_2);
return x_14;
}
else
{
if (x_14 == 0)
{
lean_dec(x_13);
lean_dec(x_2);
return x_14;
}
else
{
size_t x_15; size_t x_16; uint8_t x_17; 
x_15 = lean_usize_of_nat(x_12);
x_16 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_17 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain_spec__1_spec__1_spec__2(x_1, x_2, x_11, x_15, x_16);
return x_17;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at_____private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain_spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_2);
x_5 = l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain_spec__1_spec__1(x_1, x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_get_size(x_6);
x_9 = lean_nat_dec_lt(x_7, x_8);
if (x_9 == 0)
{
lean_dec(x_8);
lean_dec(x_2);
return x_5;
}
else
{
if (x_9 == 0)
{
lean_dec(x_8);
lean_dec(x_2);
return x_5;
}
else
{
size_t x_10; size_t x_11; uint8_t x_12; 
x_10 = lean_usize_of_nat(x_7);
x_11 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_12 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain_spec__1_spec__1_spec__2(x_1, x_2, x_6, x_10, x_11);
return x_12;
}
}
}
else
{
lean_dec(x_2);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain_spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_hasMVar(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = l_Lean_instantiateMVarsCore(x_5, x_1);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 1);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_6, 1, x_10);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc(x_2);
lean_inc(x_1);
x_8 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_1, x_2, x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_1, x_2, x_5, x_11);
return x_12;
}
else
{
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_apply_1(x_1, x_5);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = l_Lean_getExprMVarAssignment_x3f___at_____private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain_spec__0(x_10, x_4);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
lean_inc(x_10);
x_16 = lean_apply_1(x_2, x_10);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
x_19 = l_Lean_MetavarContext_getDecl(x_18, x_10);
lean_dec(x_10);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_PersistentArray_anyM___at_____private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain_spec__1(x_17, x_1, x_21);
lean_dec(x_21);
x_23 = lean_box(x_22);
lean_ctor_set(x_11, 0, x_23);
return x_11;
}
else
{
lean_object* x_24; 
lean_dec(x_10);
lean_dec(x_1);
x_24 = lean_box(x_17);
lean_ctor_set(x_11, 0, x_24);
return x_11;
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_dec(x_11);
lean_inc(x_10);
x_26 = lean_apply_1(x_2, x_10);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
x_29 = l_Lean_MetavarContext_getDecl(x_28, x_10);
lean_dec(x_10);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Lean_PersistentArray_anyM___at_____private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain_spec__1(x_27, x_1, x_31);
lean_dec(x_31);
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_25);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_10);
lean_dec(x_1);
x_35 = lean_box(x_27);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_25);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_10);
x_37 = lean_ctor_get(x_11, 1);
lean_inc(x_37);
lean_dec(x_11);
x_38 = lean_ctor_get(x_12, 0);
lean_inc(x_38);
lean_dec(x_12);
x_39 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_1, x_2, x_38, x_37);
return x_39;
}
}
case 5:
{
lean_object* x_40; uint8_t x_41; 
x_40 = l_Lean_Expr_getAppFn(x_3);
x_41 = l_Lean_Expr_isMVar(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_40);
x_42 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp(x_1, x_2, x_3, x_4);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_54; uint8_t x_55; 
lean_inc(x_3);
x_43 = l_Lean_instantiateMVars___at_____private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain_spec__5(x_3, x_4);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_46 = x_43;
} else {
 lean_dec_ref(x_43);
 x_46 = lean_box(0);
}
x_54 = l_Lean_Expr_getAppFn(x_44);
x_55 = lean_expr_eqv(x_54, x_40);
lean_dec(x_54);
if (x_55 == 0)
{
if (x_41 == 0)
{
lean_dec(x_44);
goto block_53;
}
else
{
lean_dec(x_46);
lean_dec(x_40);
lean_dec(x_3);
x_3 = x_44;
x_4 = x_45;
goto _start;
}
}
else
{
lean_dec(x_44);
goto block_53;
}
block_53:
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = l_Lean_Expr_mvarId_x21(x_40);
lean_dec(x_40);
lean_inc(x_2);
x_48 = lean_apply_1(x_2, x_47);
x_49 = lean_unbox(x_48);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_46);
x_50 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp(x_1, x_2, x_3, x_45);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = lean_box(x_41);
if (lean_is_scalar(x_46)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_46;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_45);
return x_52;
}
}
}
}
case 6:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_3, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_3, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_3, 2);
lean_inc(x_59);
x_60 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_dec(x_3);
x_61 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___lam__0(x_1, x_2, x_57, x_58, x_59, x_60, x_4);
lean_dec(x_57);
return x_61;
}
case 7:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_3, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_3, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_3, 2);
lean_inc(x_64);
x_65 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_dec(x_3);
x_66 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___lam__0(x_1, x_2, x_62, x_63, x_64, x_65, x_4);
lean_dec(x_62);
return x_66;
}
case 8:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_67 = lean_ctor_get(x_3, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_3, 2);
lean_inc(x_68);
x_69 = lean_ctor_get(x_3, 3);
lean_inc(x_69);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_70 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_1, x_2, x_67, x_4);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_unbox(x_71);
lean_dec(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
lean_inc(x_2);
lean_inc(x_1);
x_74 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_1, x_2, x_68, x_73);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_unbox(x_75);
lean_dec(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_78 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_1, x_2, x_69, x_77);
return x_78;
}
else
{
lean_dec(x_69);
lean_dec(x_2);
lean_dec(x_1);
return x_74;
}
}
else
{
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_2);
lean_dec(x_1);
return x_70;
}
}
case 10:
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_3, 1);
lean_inc(x_79);
lean_dec(x_3);
x_80 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_1, x_2, x_79, x_4);
return x_80;
}
case 11:
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_3, 2);
lean_inc(x_81);
lean_dec(x_3);
x_82 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_1, x_2, x_81, x_4);
return x_82;
}
default: 
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_4);
return x_84;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp(x_1, x_2, x_5, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_1, x_2, x_6, x_10);
return x_11;
}
else
{
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
else
{
lean_object* x_12; 
x_12 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_1, x_2, x_3, x_4);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at_____private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getExprMVarAssignment_x3f___at_____private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain_spec__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain_spec__1_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; size_t x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain_spec__1_spec__1_spec__1(x_6, x_2, x_3, x_7, x_8);
lean_dec(x_3);
x_10 = lean_box(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain_spec__1_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; size_t x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain_spec__1_spec__1_spec__2(x_6, x_2, x_3, x_7, x_8);
lean_dec(x_3);
x_10 = lean_box(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at_____private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain_spec__1_spec__1(x_4, x_2, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_____private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_PersistentArray_anyM___at_____private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain_spec__1(x_4, x_2, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_6);
lean_dec(x_6);
x_9 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___lam__0(x_1, x_2, x_3, x_4, x_5, x_8, x_7);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_DependsOn_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Expr_hasFVar(x_3);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l_Lean_Expr_hasMVar(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_1, x_2, x_3, x_4);
return x_9;
}
}
else
{
lean_object* x_10; 
x_10 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_1, x_2, x_3, x_4);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findExprDependsOn___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_findExprDependsOn___redArg___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(x_2);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_findExprDependsOn___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_17; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_23 = lean_unsigned_to_nat(8u);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_unsigned_to_nat(2u);
x_26 = lean_nat_shiftl(x_23, x_25);
x_27 = lean_unsigned_to_nat(3u);
x_28 = lean_nat_div(x_26, x_27);
lean_dec(x_26);
x_29 = l_Nat_nextPowerOfTwo(x_28);
lean_dec(x_28);
x_30 = lean_box(0);
x_31 = lean_mk_array(x_29, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_31);
lean_inc(x_7);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_7);
x_34 = l_Lean_Expr_hasFVar(x_4);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = l_Lean_Expr_hasMVar(x_4);
if (x_35 == 0)
{
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_8 = x_35;
x_9 = x_7;
goto block_16;
}
else
{
lean_object* x_36; 
lean_dec(x_7);
x_36 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_5, x_6, x_4, x_33);
x_17 = x_36;
goto block_22;
}
}
else
{
lean_object* x_37; 
lean_dec(x_7);
x_37 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_5, x_6, x_4, x_33);
x_17 = x_37;
goto block_22;
}
block_16:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_alloc_closure((void*)(l_Lean_findExprDependsOn___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = lean_box(x_8);
x_12 = lean_alloc_closure((void*)(l_Lean_findExprDependsOn___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_apply_1(x_13, x_10);
x_15 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_14, x_12);
return x_15;
}
block_22:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unbox(x_19);
lean_dec(x_19);
x_8 = x_21;
x_9 = x_20;
goto block_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findExprDependsOn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
lean_inc(x_6);
x_10 = lean_alloc_closure((void*)(l_Lean_findExprDependsOn___redArg___lam__2), 7, 6);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_6);
lean_closure_set(x_10, 3, x_3);
lean_closure_set(x_10, 4, x_4);
lean_closure_set(x_10, 5, x_5);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_findExprDependsOn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_7);
x_11 = lean_alloc_closure((void*)(l_Lean_findExprDependsOn___redArg___lam__2), 7, 6);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_7);
lean_closure_set(x_11, 3, x_4);
lean_closure_set(x_11, 4, x_5);
lean_closure_set(x_11, 5, x_6);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_findExprDependsOn___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_findExprDependsOn___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_findExprDependsOn___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_findExprDependsOn___redArg___lam__1(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_findLocalDeclDependsOn___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_17; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_23 = lean_unsigned_to_nat(8u);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_unsigned_to_nat(2u);
x_26 = lean_nat_shiftl(x_23, x_25);
x_27 = lean_unsigned_to_nat(3u);
x_28 = lean_nat_div(x_26, x_27);
lean_dec(x_26);
x_29 = l_Nat_nextPowerOfTwo(x_28);
lean_dec(x_28);
x_30 = lean_box(0);
x_31 = lean_mk_array(x_29, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_31);
lean_inc(x_7);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_7);
x_34 = l_Lean_Expr_hasFVar(x_4);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = l_Lean_Expr_hasMVar(x_4);
if (x_35 == 0)
{
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_8 = x_35;
x_9 = x_7;
goto block_16;
}
else
{
lean_object* x_36; 
lean_dec(x_7);
x_36 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_5, x_6, x_4, x_33);
x_17 = x_36;
goto block_22;
}
}
else
{
lean_object* x_37; 
lean_dec(x_7);
x_37 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_5, x_6, x_4, x_33);
x_17 = x_37;
goto block_22;
}
block_16:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_alloc_closure((void*)(l_Lean_findExprDependsOn___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = lean_box(x_8);
x_12 = lean_alloc_closure((void*)(l_Lean_findExprDependsOn___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_apply_1(x_13, x_10);
x_15 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_14, x_12);
return x_15;
}
block_22:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unbox(x_19);
lean_dec(x_19);
x_8 = x_21;
x_9 = x_20;
goto block_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findLocalDeclDependsOn___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_19; uint8_t x_24; lean_object* x_25; lean_object* x_31; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
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
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_37);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_8);
x_47 = l_Lean_Expr_hasFVar(x_7);
if (x_47 == 0)
{
uint8_t x_48; 
x_48 = l_Lean_Expr_hasMVar(x_7);
if (x_48 == 0)
{
lean_dec(x_7);
x_24 = x_48;
x_25 = x_46;
goto block_30;
}
else
{
lean_object* x_49; 
lean_inc(x_6);
lean_inc(x_5);
x_49 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_5, x_6, x_7, x_46);
x_31 = x_49;
goto block_35;
}
}
else
{
lean_object* x_50; 
lean_inc(x_6);
lean_inc(x_5);
x_50 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_5, x_6, x_7, x_46);
x_31 = x_50;
goto block_35;
}
block_18:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(x_9);
x_13 = lean_alloc_closure((void*)(l_Lean_findExprDependsOn___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_findExprDependsOn___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_14, 0, x_11);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_apply_1(x_15, x_14);
x_17 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_16, x_13);
return x_17;
}
block_23:
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unbox(x_20);
lean_dec(x_20);
x_9 = x_22;
x_10 = x_21;
goto block_18;
}
block_30:
{
if (x_24 == 0)
{
uint8_t x_26; 
x_26 = l_Lean_Expr_hasFVar(x_4);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = l_Lean_Expr_hasMVar(x_4);
if (x_27 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_9 = x_27;
x_10 = x_25;
goto block_18;
}
else
{
lean_object* x_28; 
x_28 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_5, x_6, x_4, x_25);
x_19 = x_28;
goto block_23;
}
}
else
{
lean_object* x_29; 
x_29 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_5, x_6, x_4, x_25);
x_19 = x_29;
goto block_23;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_9 = x_24;
x_10 = x_25;
goto block_18;
}
}
block_35:
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_unbox(x_32);
lean_dec(x_32);
x_24 = x_34;
x_25 = x_33;
goto block_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findLocalDeclDependsOn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_3, 3);
lean_inc(x_9);
lean_dec(x_3);
lean_inc(x_6);
lean_inc(x_2);
x_10 = lean_alloc_closure((void*)(l_Lean_findLocalDeclDependsOn___redArg___lam__2), 7, 6);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_6);
lean_closure_set(x_10, 3, x_9);
lean_closure_set(x_10, 4, x_4);
lean_closure_set(x_10, 5, x_5);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_11, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_3, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 4);
lean_inc(x_17);
lean_dec(x_3);
lean_inc(x_13);
lean_inc(x_2);
x_18 = lean_alloc_closure((void*)(l_Lean_findLocalDeclDependsOn___redArg___lam__3), 8, 7);
lean_closure_set(x_18, 0, x_15);
lean_closure_set(x_18, 1, x_2);
lean_closure_set(x_18, 2, x_13);
lean_closure_set(x_18, 3, x_17);
lean_closure_set(x_18, 4, x_4);
lean_closure_set(x_18, 5, x_5);
lean_closure_set(x_18, 6, x_16);
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_19, x_18);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findLocalDeclDependsOn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_4, 3);
lean_inc(x_10);
lean_dec(x_4);
lean_inc(x_7);
lean_inc(x_3);
x_11 = lean_alloc_closure((void*)(l_Lean_findLocalDeclDependsOn___redArg___lam__2), 7, 6);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_7);
lean_closure_set(x_11, 3, x_10);
lean_closure_set(x_11, 4, x_5);
lean_closure_set(x_11, 5, x_6);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_12, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_4, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_4, 4);
lean_inc(x_18);
lean_dec(x_4);
lean_inc(x_14);
lean_inc(x_3);
x_19 = lean_alloc_closure((void*)(l_Lean_findLocalDeclDependsOn___redArg___lam__3), 8, 7);
lean_closure_set(x_19, 0, x_16);
lean_closure_set(x_19, 1, x_3);
lean_closure_set(x_19, 2, x_14);
lean_closure_set(x_19, 3, x_18);
lean_closure_set(x_19, 4, x_5);
lean_closure_set(x_19, 5, x_6);
lean_closure_set(x_19, 6, x_17);
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
lean_dec(x_3);
x_21 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_20, x_19);
return x_21;
}
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___redArg___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_17; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_23 = lean_unsigned_to_nat(8u);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_unsigned_to_nat(2u);
x_26 = lean_nat_shiftl(x_23, x_25);
x_27 = lean_unsigned_to_nat(3u);
x_28 = lean_nat_div(x_26, x_27);
lean_dec(x_26);
x_29 = l_Nat_nextPowerOfTwo(x_28);
lean_dec(x_28);
x_30 = lean_box(0);
x_31 = lean_mk_array(x_29, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_31);
lean_inc(x_7);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_7);
x_34 = l_Lean_Expr_hasFVar(x_4);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = l_Lean_Expr_hasMVar(x_4);
if (x_35 == 0)
{
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_8 = x_35;
x_9 = x_7;
goto block_16;
}
else
{
lean_object* x_36; 
lean_dec(x_7);
x_36 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_5, x_6, x_4, x_33);
x_17 = x_36;
goto block_22;
}
}
else
{
lean_object* x_37; 
lean_dec(x_7);
x_37 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_5, x_6, x_4, x_33);
x_17 = x_37;
goto block_22;
}
block_16:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_alloc_closure((void*)(l_Lean_findExprDependsOn___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = lean_box(x_8);
x_12 = lean_alloc_closure((void*)(l_Lean_findExprDependsOn___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_apply_1(x_13, x_10);
x_15 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_14, x_12);
return x_15;
}
block_22:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unbox(x_19);
lean_dec(x_19);
x_8 = x_21;
x_9 = x_20;
goto block_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_alloc_closure((void*)(l_Lean_exprDependsOn___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_exprDependsOn___redArg___lam__1___boxed), 1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_7);
x_11 = lean_alloc_closure((void*)(l_Lean_exprDependsOn___redArg___lam__4), 7, 6);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_7);
lean_closure_set(x_11, 3, x_3);
lean_closure_set(x_11, 4, x_5);
lean_closure_set(x_11, 5, x_6);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_exprDependsOn___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_exprDependsOn___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___redArg___lam__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_exprDependsOn___redArg___lam__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_dependsOn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_exprDependsOn___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_dependsOn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_exprDependsOn___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_17; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_23 = lean_unsigned_to_nat(8u);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_unsigned_to_nat(2u);
x_26 = lean_nat_shiftl(x_23, x_25);
x_27 = lean_unsigned_to_nat(3u);
x_28 = lean_nat_div(x_26, x_27);
lean_dec(x_26);
x_29 = l_Nat_nextPowerOfTwo(x_28);
lean_dec(x_28);
x_30 = lean_box(0);
x_31 = lean_mk_array(x_29, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_31);
lean_inc(x_7);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_7);
x_34 = l_Lean_Expr_hasFVar(x_4);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = l_Lean_Expr_hasMVar(x_4);
if (x_35 == 0)
{
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_8 = x_35;
x_9 = x_7;
goto block_16;
}
else
{
lean_object* x_36; 
lean_dec(x_7);
x_36 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_5, x_6, x_4, x_33);
x_17 = x_36;
goto block_22;
}
}
else
{
lean_object* x_37; 
lean_dec(x_7);
x_37 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_5, x_6, x_4, x_33);
x_17 = x_37;
goto block_22;
}
block_16:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_alloc_closure((void*)(l_Lean_findExprDependsOn___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = lean_box(x_8);
x_12 = lean_alloc_closure((void*)(l_Lean_findExprDependsOn___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_apply_1(x_13, x_10);
x_15 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_14, x_12);
return x_15;
}
block_22:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unbox(x_19);
lean_dec(x_19);
x_8 = x_21;
x_9 = x_20;
goto block_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_19; uint8_t x_24; lean_object* x_25; lean_object* x_31; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
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
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_37);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_8);
x_47 = l_Lean_Expr_hasFVar(x_7);
if (x_47 == 0)
{
uint8_t x_48; 
x_48 = l_Lean_Expr_hasMVar(x_7);
if (x_48 == 0)
{
lean_dec(x_7);
x_24 = x_48;
x_25 = x_46;
goto block_30;
}
else
{
lean_object* x_49; 
lean_inc(x_6);
lean_inc(x_5);
x_49 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_5, x_6, x_7, x_46);
x_31 = x_49;
goto block_35;
}
}
else
{
lean_object* x_50; 
lean_inc(x_6);
lean_inc(x_5);
x_50 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_5, x_6, x_7, x_46);
x_31 = x_50;
goto block_35;
}
block_18:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(x_9);
x_13 = lean_alloc_closure((void*)(l_Lean_findExprDependsOn___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_findExprDependsOn___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_14, 0, x_11);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_apply_1(x_15, x_14);
x_17 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_16, x_13);
return x_17;
}
block_23:
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unbox(x_20);
lean_dec(x_20);
x_9 = x_22;
x_10 = x_21;
goto block_18;
}
block_30:
{
if (x_24 == 0)
{
uint8_t x_26; 
x_26 = l_Lean_Expr_hasFVar(x_4);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = l_Lean_Expr_hasMVar(x_4);
if (x_27 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_9 = x_27;
x_10 = x_25;
goto block_18;
}
else
{
lean_object* x_28; 
x_28 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_5, x_6, x_4, x_25);
x_19 = x_28;
goto block_23;
}
}
else
{
lean_object* x_29; 
x_29 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_5, x_6, x_4, x_25);
x_19 = x_29;
goto block_23;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_9 = x_24;
x_10 = x_25;
goto block_18;
}
}
block_35:
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_unbox(x_32);
lean_dec(x_32);
x_24 = x_34;
x_25 = x_33;
goto block_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_exprDependsOn___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_exprDependsOn___redArg___lam__1___boxed), 1, 0);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_3, 3);
lean_inc(x_10);
lean_dec(x_3);
lean_inc(x_7);
lean_inc(x_2);
x_11 = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___redArg___lam__4), 7, 6);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_7);
lean_closure_set(x_11, 3, x_10);
lean_closure_set(x_11, 4, x_5);
lean_closure_set(x_11, 5, x_6);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_12, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_3, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 4);
lean_inc(x_18);
lean_dec(x_3);
lean_inc(x_14);
lean_inc(x_2);
x_19 = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___redArg___lam__2), 8, 7);
lean_closure_set(x_19, 0, x_16);
lean_closure_set(x_19, 1, x_2);
lean_closure_set(x_19, 2, x_14);
lean_closure_set(x_19, 3, x_18);
lean_closure_set(x_19, 4, x_5);
lean_closure_set(x_19, 5, x_6);
lean_closure_set(x_19, 6, x_17);
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
lean_dec(x_2);
x_21 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_20, x_19);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_localDeclDependsOn___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn_x27___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Expr_mvarId_x21(x_1);
x_4 = lean_name_eq(x_3, x_2);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn_x27___redArg___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn_x27___redArg___lam__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Expr_fvarId_x21(x_1);
x_4 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_3, x_2);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Expr_isFVar(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l_Lean_Expr_isMVar(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(x_6);
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_alloc_closure((void*)(l_Lean_exprDependsOn_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_11, 0, x_4);
x_12 = lean_box(x_5);
x_13 = lean_alloc_closure((void*)(l_Lean_exprDependsOn_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
lean_inc(x_14);
x_18 = lean_alloc_closure((void*)(l_Lean_exprDependsOn___redArg___lam__4), 7, 6);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_2);
lean_closure_set(x_18, 2, x_14);
lean_closure_set(x_18, 3, x_3);
lean_closure_set(x_18, 4, x_13);
lean_closure_set(x_18, 5, x_11);
x_19 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_15, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_alloc_closure((void*)(l_Lean_exprDependsOn___redArg___lam__1___boxed), 1, 0);
x_21 = lean_alloc_closure((void*)(l_Lean_exprDependsOn_x27___redArg___lam__6___boxed), 2, 1);
lean_closure_set(x_21, 0, x_4);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
lean_dec(x_1);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
lean_inc(x_22);
x_26 = lean_alloc_closure((void*)(l_Lean_exprDependsOn___redArg___lam__4), 7, 6);
lean_closure_set(x_26, 0, x_25);
lean_closure_set(x_26, 1, x_2);
lean_closure_set(x_26, 2, x_22);
lean_closure_set(x_26, 3, x_3);
lean_closure_set(x_26, 4, x_21);
lean_closure_set(x_26, 5, x_20);
x_27 = lean_apply_4(x_22, lean_box(0), lean_box(0), x_23, x_26);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_exprDependsOn_x27___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn_x27___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_exprDependsOn_x27___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn_x27___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_exprDependsOn_x27___redArg___lam__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn_x27___redArg___lam__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_exprDependsOn_x27___redArg___lam__6(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Expr_isFVar(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l_Lean_Expr_isMVar(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(x_6);
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_alloc_closure((void*)(l_Lean_exprDependsOn_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_11, 0, x_4);
x_12 = lean_box(x_5);
x_13 = lean_alloc_closure((void*)(l_Lean_exprDependsOn_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_13, 0, x_12);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_3, 3);
lean_inc(x_17);
lean_dec(x_3);
lean_inc(x_14);
lean_inc(x_2);
x_18 = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___redArg___lam__4), 7, 6);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_2);
lean_closure_set(x_18, 2, x_14);
lean_closure_set(x_18, 3, x_17);
lean_closure_set(x_18, 4, x_13);
lean_closure_set(x_18, 5, x_11);
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_19, x_18);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get(x_3, 3);
lean_inc(x_24);
x_25 = lean_ctor_get(x_3, 4);
lean_inc(x_25);
lean_dec(x_3);
lean_inc(x_21);
lean_inc(x_2);
x_26 = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___redArg___lam__2), 8, 7);
lean_closure_set(x_26, 0, x_23);
lean_closure_set(x_26, 1, x_2);
lean_closure_set(x_26, 2, x_21);
lean_closure_set(x_26, 3, x_25);
lean_closure_set(x_26, 4, x_13);
lean_closure_set(x_26, 5, x_11);
lean_closure_set(x_26, 6, x_24);
x_27 = lean_ctor_get(x_2, 0);
lean_inc(x_27);
lean_dec(x_2);
x_28 = lean_apply_4(x_21, lean_box(0), lean_box(0), x_27, x_26);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_alloc_closure((void*)(l_Lean_exprDependsOn_x27___redArg___lam__6___boxed), 2, 1);
lean_closure_set(x_29, 0, x_4);
x_30 = lean_alloc_closure((void*)(l_Lean_exprDependsOn___redArg___lam__1___boxed), 1, 0);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
lean_dec(x_1);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get(x_3, 3);
lean_inc(x_34);
lean_dec(x_3);
lean_inc(x_31);
lean_inc(x_2);
x_35 = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___redArg___lam__4), 7, 6);
lean_closure_set(x_35, 0, x_33);
lean_closure_set(x_35, 1, x_2);
lean_closure_set(x_35, 2, x_31);
lean_closure_set(x_35, 3, x_34);
lean_closure_set(x_35, 4, x_29);
lean_closure_set(x_35, 5, x_30);
x_36 = lean_ctor_get(x_2, 0);
lean_inc(x_36);
lean_dec(x_2);
x_37 = lean_apply_4(x_31, lean_box(0), lean_box(0), x_36, x_35);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_1, 0);
lean_inc(x_39);
lean_dec(x_1);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_ctor_get(x_3, 3);
lean_inc(x_41);
x_42 = lean_ctor_get(x_3, 4);
lean_inc(x_42);
lean_dec(x_3);
lean_inc(x_38);
lean_inc(x_2);
x_43 = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___redArg___lam__2), 8, 7);
lean_closure_set(x_43, 0, x_40);
lean_closure_set(x_43, 1, x_2);
lean_closure_set(x_43, 2, x_38);
lean_closure_set(x_43, 3, x_42);
lean_closure_set(x_43, 4, x_29);
lean_closure_set(x_43, 5, x_30);
lean_closure_set(x_43, 6, x_41);
x_44 = lean_ctor_get(x_2, 0);
lean_inc(x_44);
lean_dec(x_2);
x_45 = lean_apply_4(x_38, lean_box(0), lean_box(0), x_44, x_43);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_localDeclDependsOn_x27___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_dependsOnPred___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
lean_inc(x_6);
x_10 = lean_alloc_closure((void*)(l_Lean_findExprDependsOn___redArg___lam__2), 7, 6);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_6);
lean_closure_set(x_10, 3, x_3);
lean_closure_set(x_10, 4, x_4);
lean_closure_set(x_10, 5, x_5);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_dependsOnPred(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_dependsOnPred___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOnPred___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_3, 3);
lean_inc(x_9);
lean_dec(x_3);
lean_inc(x_6);
lean_inc(x_2);
x_10 = lean_alloc_closure((void*)(l_Lean_findLocalDeclDependsOn___redArg___lam__2), 7, 6);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_6);
lean_closure_set(x_10, 3, x_9);
lean_closure_set(x_10, 4, x_4);
lean_closure_set(x_10, 5, x_5);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_11, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_3, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 4);
lean_inc(x_17);
lean_dec(x_3);
lean_inc(x_13);
lean_inc(x_2);
x_18 = lean_alloc_closure((void*)(l_Lean_findLocalDeclDependsOn___redArg___lam__3), 8, 7);
lean_closure_set(x_18, 0, x_15);
lean_closure_set(x_18, 1, x_2);
lean_closure_set(x_18, 2, x_13);
lean_closure_set(x_18, 3, x_17);
lean_closure_set(x_18, 4, x_4);
lean_closure_set(x_18, 5, x_5);
lean_closure_set(x_18, 6, x_16);
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_19, x_18);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOnPred(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_localDeclDependsOnPred___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lean_mk_metavar_ctx(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
lean_inc(x_3);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_3);
lean_inc(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_3);
lean_inc(x_3);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_3);
lean_inc(x_3);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_3);
x_10 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_2);
lean_ctor_set(x_10, 2, x_2);
lean_ctor_set(x_10, 3, x_4);
lean_ctor_set(x_10, 4, x_5);
lean_ctor_set(x_10, 5, x_6);
lean_ctor_set(x_10, 6, x_7);
lean_ctor_set(x_10, 7, x_8);
lean_ctor_set(x_10, 8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; size_t x_7; lean_object* x_8; size_t x_9; lean_object* x_10; 
x_4 = l_Lean_Name_instBEq;
x_5 = l_Lean_instHashableName;
x_6 = l_Lean_Name_hash___override(x_2);
x_7 = lean_uint64_to_usize(x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert_spec__0___redArg(x_4, x_5, x_1, x_7, x_9, x_2, x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_addExprMVarDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_24; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_11, x_12);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 4);
lean_inc(x_15);
lean_inc(x_9);
lean_inc(x_3);
x_16 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_4);
lean_ctor_set(x_16, 2, x_6);
lean_ctor_set(x_16, 3, x_9);
lean_ctor_set(x_16, 4, x_5);
lean_ctor_set(x_16, 5, x_8);
lean_ctor_set(x_16, 6, x_11);
lean_ctor_set_uint8(x_16, sizeof(void*)*7, x_7);
lean_inc(x_2);
x_17 = l_Lean_PersistentHashMap_insert___at___Lean_assignExp_spec__0___redArg(x_15, x_2, x_16);
x_24 = l_Lean_Name_isAnonymous(x_3);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_1, 5);
lean_inc(x_25);
x_26 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0___redArg(x_25, x_3, x_2);
x_18 = x_26;
goto block_23;
}
else
{
lean_object* x_27; 
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_ctor_get(x_1, 5);
lean_inc(x_27);
x_18 = x_27;
goto block_23;
}
block_23:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_1, 6);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 7);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 8);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_22, 0, x_9);
lean_ctor_set(x_22, 1, x_10);
lean_ctor_set(x_22, 2, x_13);
lean_ctor_set(x_22, 3, x_14);
lean_ctor_set(x_22, 4, x_17);
lean_ctor_set(x_22, 5, x_18);
lean_ctor_set(x_22, 6, x_19);
lean_ctor_set(x_22, 7, x_20);
lean_ctor_set(x_22, 8, x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_addExprMVarDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_7);
lean_dec(x_7);
x_10 = l_Lean_MetavarContext_addExprMVarDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_addExprMVarDeclExp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_MetavarContext_addExprMVarDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_addExprMVarDeclExp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_7);
lean_dec(x_7);
x_9 = l_Lean_MetavarContext_addExprMVarDeclExp(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_addLevelMVarDecl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_inc(x_3);
x_7 = l_Lean_PersistentHashMap_insert___at___Lean_assignLevelMVarExp_spec__0___redArg(x_6, x_2, x_3);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 5);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 6);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 7);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 8);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_4);
lean_ctor_set(x_13, 2, x_5);
lean_ctor_set(x_13, 3, x_7);
lean_ctor_set(x_13, 4, x_8);
lean_ctor_set(x_13, 5, x_9);
lean_ctor_set(x_13, 6, x_10);
lean_ctor_set(x_13, 7, x_11);
lean_ctor_set(x_13, 8, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_findDecl_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 4);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0___redArg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_findDecl_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MetavarContext_findDecl_x3f(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget(x_1, x_3);
x_9 = lean_name_eq(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget(x_2, x_3);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0_spec__0_spec__0___redArg(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; size_t x_10; size_t x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Lean_PersistentHashMap_instInhabitedEntry(lean_box(0), lean_box(0), lean_box(0));
x_7 = lean_unsigned_to_nat(5u);
x_8 = lean_usize_of_nat(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_shift_left(x_10, x_8);
x_12 = lean_usize_sub(x_11, x_10);
x_13 = lean_usize_land(x_2, x_12);
x_14 = lean_usize_to_nat(x_13);
x_15 = lean_array_get(x_6, x_5, x_14);
lean_dec(x_14);
lean_dec(x_5);
switch (lean_obj_tag(x_15)) {
case 0:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_name_eq(x_3, x_16);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_17);
lean_free_object(x_1);
x_19 = lean_box(0);
return x_19;
}
else
{
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_17);
return x_1;
}
}
case 1:
{
lean_object* x_20; size_t x_21; 
lean_free_object(x_1);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_usize_shift_right(x_2, x_8);
x_1 = x_20;
x_2 = x_21;
goto _start;
}
default: 
{
lean_object* x_23; 
lean_free_object(x_1);
x_23 = lean_box(0);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; lean_object* x_28; size_t x_29; size_t x_30; size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
lean_dec(x_1);
x_25 = l_Lean_PersistentHashMap_instInhabitedEntry(lean_box(0), lean_box(0), lean_box(0));
x_26 = lean_unsigned_to_nat(5u);
x_27 = lean_usize_of_nat(x_26);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_usize_of_nat(x_28);
x_30 = lean_usize_shift_left(x_29, x_27);
x_31 = lean_usize_sub(x_30, x_29);
x_32 = lean_usize_land(x_2, x_31);
x_33 = lean_usize_to_nat(x_32);
x_34 = lean_array_get(x_25, x_24, x_33);
lean_dec(x_33);
lean_dec(x_24);
switch (lean_obj_tag(x_34)) {
case 0:
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_name_eq(x_3, x_35);
lean_dec(x_35);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_36);
x_38 = lean_box(0);
return x_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_36);
return x_39;
}
}
case 1:
{
lean_object* x_40; size_t x_41; 
x_40 = lean_ctor_get(x_34, 0);
lean_inc(x_40);
lean_dec(x_34);
x_41 = lean_usize_shift_right(x_2, x_27);
x_1 = x_40;
x_2 = x_41;
goto _start;
}
default: 
{
lean_object* x_43; 
x_43 = lean_box(0);
return x_43;
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
lean_dec(x_1);
x_46 = lean_unsigned_to_nat(0u);
x_47 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0_spec__0_spec__0___redArg(x_44, x_45, x_46, x_3);
lean_dec(x_45);
lean_dec(x_44);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l_Lean_Name_hash___override(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0_spec__0___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_findUserName_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 5);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0___redArg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0_spec__0___redArg(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0_spec__0(x_1, x_2, x_5, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_findUserName_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MetavarContext_findUserName_x3f(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_modifyExprMVarDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 4);
lean_inc(x_4);
lean_inc(x_4);
x_5 = l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_getExprAssignmentCore_x3f_spec__0___redArg(x_4, x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
x_11 = lean_apply_1(x_3, x_6);
x_12 = l_Lean_PersistentHashMap_insert___at___Lean_assignExp_spec__0___redArg(x_4, x_2, x_11);
x_13 = lean_ctor_get(x_1, 5);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 6);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 7);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 8);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_8);
lean_ctor_set(x_17, 2, x_9);
lean_ctor_set(x_17, 3, x_10);
lean_ctor_set(x_17, 4, x_12);
lean_ctor_set(x_17, 5, x_13);
lean_ctor_set(x_17, 6, x_14);
lean_ctor_set(x_17, 7, x_15);
lean_ctor_set(x_17, 8, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_setMVarKind(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_inc(x_1);
x_4 = l_Lean_MetavarContext_getDecl(x_1, x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 4);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 5);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 6);
lean_inc(x_16);
lean_dec(x_4);
x_17 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_12);
lean_ctor_set(x_17, 3, x_13);
lean_ctor_set(x_17, 4, x_14);
lean_ctor_set(x_17, 5, x_15);
lean_ctor_set(x_17, 6, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*7, x_3);
x_18 = l_Lean_PersistentHashMap_insert___at___Lean_assignExp_spec__0___redArg(x_9, x_2, x_17);
x_19 = lean_ctor_get(x_1, 5);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 6);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 7);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 8);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_6);
lean_ctor_set(x_23, 2, x_7);
lean_ctor_set(x_23, 3, x_8);
lean_ctor_set(x_23, 4, x_18);
lean_ctor_set(x_23, 5, x_19);
lean_ctor_set(x_23, 6, x_20);
lean_ctor_set(x_23, 7, x_21);
lean_ctor_set(x_23, 8, x_22);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_setMVarKind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_MetavarContext_setMVarKind(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___Lean_MetavarContext_setMVarUserName_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; lean_object* x_6; 
x_3 = l_Lean_Name_instBEq;
x_4 = l_Lean_Name_hash___override(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Lean_PersistentHashMap_eraseAux___at___Lean_PersistentHashMap_erase_spec__0___redArg(x_3, x_1, x_5, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___Lean_MetavarContext_setMVarUserName_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_erase___at___Lean_MetavarContext_setMVarUserName_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_setMVarUserName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_inc(x_1);
x_4 = l_Lean_MetavarContext_getDecl(x_1, x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 4);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_4, sizeof(void*)*7);
x_15 = lean_ctor_get(x_4, 5);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 6);
lean_inc(x_16);
lean_inc(x_3);
x_17 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_10);
lean_ctor_set(x_17, 2, x_11);
lean_ctor_set(x_17, 3, x_12);
lean_ctor_set(x_17, 4, x_13);
lean_ctor_set(x_17, 5, x_15);
lean_ctor_set(x_17, 6, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*7, x_14);
lean_inc(x_2);
x_18 = l_Lean_PersistentHashMap_insert___at___Lean_assignExp_spec__0___redArg(x_9, x_2, x_17);
x_25 = lean_ctor_get(x_1, 5);
lean_inc(x_25);
x_26 = lean_ctor_get(x_4, 0);
lean_inc(x_26);
lean_dec(x_4);
x_27 = l_Lean_PersistentHashMap_erase___at___Lean_MetavarContext_setMVarUserName_spec__0___redArg(x_25, x_26);
x_28 = l_Lean_Name_isAnonymous(x_3);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0___redArg(x_27, x_3, x_2);
x_19 = x_29;
goto block_24;
}
else
{
lean_dec(x_3);
lean_dec(x_2);
x_19 = x_27;
goto block_24;
}
block_24:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 6);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 7);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 8);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_6);
lean_ctor_set(x_23, 2, x_7);
lean_ctor_set(x_23, 3, x_8);
lean_ctor_set(x_23, 4, x_18);
lean_ctor_set(x_23, 5, x_19);
lean_ctor_set(x_23, 6, x_20);
lean_ctor_set(x_23, 7, x_21);
lean_ctor_set(x_23, 8, x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_setMVarUserNameTemporarily(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_inc(x_1);
x_4 = l_Lean_MetavarContext_getDecl(x_1, x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 4);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_4, sizeof(void*)*7);
x_15 = lean_ctor_get(x_4, 5);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 6);
lean_inc(x_16);
lean_dec(x_4);
x_17 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_10);
lean_ctor_set(x_17, 2, x_11);
lean_ctor_set(x_17, 3, x_12);
lean_ctor_set(x_17, 4, x_13);
lean_ctor_set(x_17, 5, x_15);
lean_ctor_set(x_17, 6, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*7, x_14);
x_18 = l_Lean_PersistentHashMap_insert___at___Lean_assignExp_spec__0___redArg(x_9, x_2, x_17);
x_19 = lean_ctor_get(x_1, 5);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 6);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 7);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 8);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_6);
lean_ctor_set(x_23, 2, x_7);
lean_ctor_set(x_23, 3, x_8);
lean_ctor_set(x_23, 4, x_18);
lean_ctor_set(x_23, 5, x_19);
lean_ctor_set(x_23, 6, x_20);
lean_ctor_set(x_23, 7, x_21);
lean_ctor_set(x_23, 8, x_22);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_setMVarType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_inc(x_1);
x_4 = l_Lean_MetavarContext_getDecl(x_1, x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 4);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_4, sizeof(void*)*7);
x_15 = lean_ctor_get(x_4, 5);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 6);
lean_inc(x_16);
lean_dec(x_4);
x_17 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_3);
lean_ctor_set(x_17, 3, x_12);
lean_ctor_set(x_17, 4, x_13);
lean_ctor_set(x_17, 5, x_15);
lean_ctor_set(x_17, 6, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*7, x_14);
x_18 = l_Lean_PersistentHashMap_insert___at___Lean_assignExp_spec__0___redArg(x_9, x_2, x_17);
x_19 = lean_ctor_get(x_1, 5);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 6);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 7);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 8);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_6);
lean_ctor_set(x_23, 2, x_7);
lean_ctor_set(x_23, 3, x_8);
lean_ctor_set(x_23, 4, x_18);
lean_ctor_set(x_23, 5, x_19);
lean_ctor_set(x_23, 6, x_20);
lean_ctor_set(x_23, 7, x_21);
lean_ctor_set(x_23, 8, x_22);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_modifyExprMVarLCtx___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_2, sizeof(void*)*7);
x_10 = lean_ctor_get(x_2, 5);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 6);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_5);
lean_ctor_set(x_12, 2, x_6);
lean_ctor_set(x_12, 3, x_7);
lean_ctor_set(x_12, 4, x_8);
lean_ctor_set(x_12, 5, x_10);
lean_ctor_set(x_12, 6, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*7, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_modifyExprMVarLCtx(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_MetavarContext_modifyExprMVarLCtx___lam__0), 2, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = l_Lean_MetavarContext_modifyExprMVarDecl(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_setFVarKind___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_LocalContext_setKind(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_setFVarKind(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box(x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_MetavarContext_setFVarKind___lam__0___boxed), 3, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_5);
x_7 = l_Lean_MetavarContext_modifyExprMVarLCtx(x_1, x_2, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_setFVarKind___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_MetavarContext_setFVarKind___lam__0(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_setFVarKind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_MetavarContext_setFVarKind(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_setFVarBinderInfo___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_LocalContext_setBinderInfo(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_setFVarBinderInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box(x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_MetavarContext_setFVarBinderInfo___lam__0___boxed), 3, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_5);
x_7 = l_Lean_MetavarContext_modifyExprMVarLCtx(x_1, x_2, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_setFVarBinderInfo___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_MetavarContext_setFVarBinderInfo___lam__0(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_setFVarBinderInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_MetavarContext_setFVarBinderInfo(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_findLevelDepth_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0___redArg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_findLevelDepth_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MetavarContext_findLevelDepth_x3f(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_getLevelDepth(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MetavarContext_findLevelDepth_x3f(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_mk_string_unchecked("Lean.MetavarContext", 19, 19);
x_5 = lean_mk_string_unchecked("Lean.MetavarContext.getLevelDepth", 33, 33);
x_6 = lean_unsigned_to_nat(874u);
x_7 = lean_unsigned_to_nat(14u);
x_8 = lean_mk_string_unchecked("unknown metavariable", 20, 20);
x_9 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_10 = l_panic___at___String_toNat_x21_spec__0(x_9);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_getLevelDepth___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MetavarContext_getLevelDepth(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_MetavarContext_isAnonymousMVar(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MetavarContext_findDecl_x3f(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Name_isAnonymous(x_7);
lean_dec(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_isAnonymousMVar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_MetavarContext_isAnonymousMVar(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_incDepth(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_dec(x_3);
if (x_2 == 0)
{
lean_inc(x_5);
x_6 = x_5;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_6 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 5);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 6);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 7);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 8);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_6);
lean_ctor_set(x_14, 2, x_7);
lean_ctor_set(x_14, 3, x_8);
lean_ctor_set(x_14, 4, x_9);
lean_ctor_set(x_14, 5, x_10);
lean_ctor_set(x_14, 6, x_11);
lean_ctor_set(x_14, 7, x_12);
lean_ctor_set(x_14, 8, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_incDepth___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_MetavarContext_incDepth(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_instToStringException___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_12; lean_object* x_13; 
x_4 = lean_mk_string_unchecked("'", 1, 1);
x_12 = l_Lean_LocalContext_getFVar_x21(x_2, x_3);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_dec(x_12);
x_5 = x_13;
goto block_11;
block_11:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_box(1);
x_7 = lean_unbox(x_6);
x_8 = l_Lean_Name_toString(x_5, x_7, x_1);
lean_inc(x_4);
x_9 = lean_string_append(x_4, x_8);
lean_dec(x_8);
x_10 = lean_string_append(x_9, x_4);
lean_dec(x_4);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_instToStringException___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; lean_object* x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 3);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_alloc_closure((void*)(l_Lean_MetavarContext_MkBinding_instToStringException___lam__1___boxed), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_4);
x_8 = lean_mk_string_unchecked("failed to revert ", 17, 17);
x_9 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_10 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_11 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_12 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_13 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_14 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_15 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_10);
x_17 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_12);
lean_ctor_set(x_17, 3, x_13);
lean_ctor_set(x_17, 4, x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
x_19 = lean_array_size(x_5);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_usize_of_nat(x_20);
x_22 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_18, x_7, x_19, x_21, x_5);
x_23 = lean_mk_string_unchecked("#", 1, 1);
x_24 = lean_array_to_list(x_22);
x_25 = l_List_toString(lean_box(0), x_2, x_24);
x_26 = lean_string_append(x_23, x_25);
lean_dec(x_25);
x_27 = lean_string_append(x_8, x_26);
lean_dec(x_26);
x_28 = lean_mk_string_unchecked(", '", 3, 3);
x_29 = lean_string_append(x_27, x_28);
lean_dec(x_28);
x_30 = lean_string_append(x_29, x_6);
x_31 = lean_mk_string_unchecked("' depends on them, and it is an auxiliary declaration created by the elaborator", 79, 79);
x_32 = lean_string_append(x_30, x_31);
lean_dec(x_31);
x_33 = lean_mk_string_unchecked(" (possible solution: use tactic 'clear' to remove '", 51, 51);
x_34 = lean_string_append(x_32, x_33);
lean_dec(x_33);
x_35 = lean_string_append(x_34, x_6);
lean_dec(x_6);
x_36 = lean_mk_string_unchecked("' from local context)", 21, 21);
x_37 = lean_string_append(x_35, x_36);
lean_dec(x_36);
return x_37;
}
}
static lean_object* _init_l_Lean_MetavarContext_MkBinding_instToStringException() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_instantiateLCtxMVars___redArg___lam__1___boxed), 1, 0);
x_2 = lean_alloc_closure((void*)(l_instToStringString___lam__0___boxed), 1, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_MetavarContext_MkBinding_instToStringException___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_instToStringException___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MetavarContext_MkBinding_instToStringException___lam__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_instMonadMCtxM___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_instMonadMCtxM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_instMonadMCtxM___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_box(0);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_apply_1(x_1, x_5);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 3);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_8);
lean_ctor_set(x_10, 3, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_instMonadMCtxM___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_1(x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
lean_ctor_set(x_6, 0, x_3);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
else
{
lean_dec(x_3);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_instMonadMCtxM___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_1(x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_4, x_9, x_8);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_apply_1(x_7, x_12);
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
x_16 = lean_apply_1(x_7, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_dec(x_7);
return x_10;
}
}
else
{
uint8_t x_18; 
lean_dec(x_4);
x_18 = !lean_is_exclusive(x_6);
if (x_18 == 0)
{
return x_6;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_6, 0);
x_20 = lean_ctor_get(x_6, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_6);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_instMonadMCtxM___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_1(x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_4, x_9, x_8);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_7);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_dec(x_7);
return x_10;
}
}
else
{
lean_dec(x_4);
return x_6;
}
}
}
static lean_object* _init_l_Lean_MetavarContext_MkBinding_instMonadMCtxM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_1 = lean_alloc_closure((void*)(l_Lean_MetavarContext_MkBinding_instMonadMCtxM___lam__0___boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_MetavarContext_MkBinding_instMonadMCtxM___lam__1___boxed), 3, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_MetavarContext_MkBinding_instMonadMCtxM___lam__2___boxed), 3, 0);
x_4 = lean_alloc_closure((void*)(l_Lean_MetavarContext_MkBinding_instMonadMCtxM___lam__3), 5, 0);
x_5 = lean_alloc_closure((void*)(l_Lean_MetavarContext_MkBinding_instMonadMCtxM___lam__4), 5, 0);
x_6 = lean_alloc_closure((void*)(l_Lean_MetavarContext_MkBinding_instMonadMCtxM___lam__5), 5, 0);
x_7 = lean_alloc_closure((void*)(l_EStateM_map), 7, 2);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, lean_box(0));
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_alloc_closure((void*)(l_EStateM_pure), 5, 2);
lean_closure_set(x_9, 0, lean_box(0));
lean_closure_set(x_9, 1, lean_box(0));
x_10 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_10, 0, lean_box(0));
lean_closure_set(x_10, 1, lean_box(0));
x_11 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_5);
lean_ctor_set(x_11, 3, x_6);
lean_ctor_set(x_11, 4, x_10);
x_12 = lean_alloc_closure((void*)(l_EStateM_bind), 7, 2);
lean_closure_set(x_12, 0, lean_box(0));
lean_closure_set(x_12, 1, lean_box(0));
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_14, 0, lean_box(0));
lean_closure_set(x_14, 1, lean_box(0));
lean_closure_set(x_14, 2, x_13);
lean_closure_set(x_14, 3, lean_box(0));
lean_closure_set(x_14, 4, lean_box(0));
lean_closure_set(x_14, 5, x_1);
lean_closure_set(x_14, 6, x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_instMonadMCtxM___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MetavarContext_MkBinding_instMonadMCtxM___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_instMonadMCtxM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MetavarContext_MkBinding_instMonadMCtxM___lam__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_instMonadMCtxM___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MetavarContext_MkBinding_instMonadMCtxM___lam__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkFreshBinderName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_4, x_6);
x_8 = lean_ctor_get(x_3, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 3);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_8);
lean_ctor_set(x_10, 3, x_9);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = l_Lean_addMacroScope(x_11, x_1, x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_preserveOrder(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_4 = lean_box(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_preserveOrder___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MetavarContext_MkBinding_preserveOrder(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_instMonadHashMapCacheAdapterExprStructEqExprM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_instMonadHashMapCacheAdapterExprStructEqExprM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_box(0);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 3);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_apply_1(x_1, x_8);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_7);
lean_ctor_set(x_10, 3, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
static lean_object* _init_l_Lean_MetavarContext_MkBinding_instMonadHashMapCacheAdapterExprStructEqExprM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_1 = lean_alloc_closure((void*)(l_Lean_MetavarContext_MkBinding_instMonadMCtxM___lam__0___boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_MetavarContext_MkBinding_instMonadHashMapCacheAdapterExprStructEqExprM___lam__1___boxed), 3, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_MetavarContext_MkBinding_instMonadHashMapCacheAdapterExprStructEqExprM___lam__0___boxed), 3, 0);
x_4 = lean_alloc_closure((void*)(l_Lean_MetavarContext_MkBinding_instMonadMCtxM___lam__3), 5, 0);
x_5 = lean_alloc_closure((void*)(l_Lean_MetavarContext_MkBinding_instMonadMCtxM___lam__4), 5, 0);
x_6 = lean_alloc_closure((void*)(l_Lean_MetavarContext_MkBinding_instMonadMCtxM___lam__5), 5, 0);
x_7 = lean_alloc_closure((void*)(l_EStateM_map), 7, 2);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, lean_box(0));
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_alloc_closure((void*)(l_EStateM_pure), 5, 2);
lean_closure_set(x_9, 0, lean_box(0));
lean_closure_set(x_9, 1, lean_box(0));
x_10 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_10, 0, lean_box(0));
lean_closure_set(x_10, 1, lean_box(0));
x_11 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_5);
lean_ctor_set(x_11, 3, x_6);
lean_ctor_set(x_11, 4, x_10);
x_12 = lean_alloc_closure((void*)(l_EStateM_bind), 7, 2);
lean_closure_set(x_12, 0, lean_box(0));
lean_closure_set(x_12, 1, lean_box(0));
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_14, 0, lean_box(0));
lean_closure_set(x_14, 1, lean_box(0));
lean_closure_set(x_14, 2, x_13);
lean_closure_set(x_14, 3, lean_box(0));
lean_closure_set(x_14, 4, lean_box(0));
lean_closure_set(x_14, 5, x_1);
lean_closure_set(x_14, 6, x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_instMonadHashMapCacheAdapterExprStructEqExprM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MetavarContext_MkBinding_instMonadHashMapCacheAdapterExprStructEqExprM___lam__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_instMonadHashMapCacheAdapterExprStructEqExprM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MetavarContext_MkBinding_instMonadHashMapCacheAdapterExprStructEqExprM___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_getLocalDeclWithSmallestIdx_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_20; uint8_t x_23; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_array_uget(x_13, x_4);
x_23 = l_Lean_Expr_isFVar(x_14);
if (x_23 == 0)
{
lean_dec(x_14);
x_6 = x_5;
goto block_11;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_inc(x_1);
x_24 = l_Lean_LocalContext_getFVar_x21(x_1, x_14);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_20 = x_25;
goto block_22;
}
block_19:
{
uint8_t x_17; 
x_17 = lean_nat_dec_lt(x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
if (x_17 == 0)
{
lean_dec(x_14);
x_6 = x_5;
goto block_11;
}
else
{
lean_object* x_18; 
lean_dec(x_5);
lean_inc(x_1);
x_18 = l_Lean_LocalContext_getFVar_x21(x_1, x_14);
lean_dec(x_14);
x_6 = x_18;
goto block_11;
}
}
block_22:
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_5, 0);
lean_inc(x_21);
x_15 = x_20;
x_16 = x_21;
goto block_19;
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
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_getLocalDeclWithSmallestIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; lean_object* x_12; size_t x_13; lean_object* x_14; 
x_3 = l_Lean_instInhabitedExpr;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get(x_3, x_2, x_4);
lean_inc(x_1);
x_6 = l_Lean_LocalContext_getFVar_x21(x_1, x_5);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_array_get_size(x_2);
x_9 = l_Array_toSubarray___redArg(x_2, x_7, x_8);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
x_11 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
x_13 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_14 = l_Subarray_forInUnsafe_loop___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_getLocalDeclWithSmallestIdx_spec__0(x_1, x_9, x_11, x_13, x_6);
lean_dec(x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_getLocalDeclWithSmallestIdx_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Subarray_forInUnsafe_loop___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_getLocalDeclWithSmallestIdx_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_Expr_fvarId_x21(x_6);
lean_dec(x_6);
x_8 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_7, x_1);
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
LEAN_EXPORT uint8_t l_Nat_anyTR_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 1)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_19; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_4, x_9);
x_11 = lean_nat_sub(x_3, x_4);
lean_dec(x_4);
x_19 = lean_ctor_get(x_1, 1);
x_12 = x_19;
goto block_18;
block_18:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = l_Lean_instInhabitedExpr;
x_14 = lean_array_get(x_13, x_2, x_11);
lean_dec(x_11);
x_15 = l_Lean_Expr_fvarId_x21(x_14);
lean_dec(x_14);
x_16 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_12, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
x_4 = x_10;
goto _start;
}
else
{
lean_dec(x_10);
return x_16;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Nat_anyTR_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Nat_anyTR_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__1___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_17; 
x_6 = lean_box(1);
x_7 = lean_array_uget(x_2, x_3);
x_17 = lean_ctor_get(x_1, 1);
x_8 = x_17;
goto block_16;
block_16:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Expr_fvarId_x21(x_7);
lean_dec(x_7);
x_10 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_8, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; size_t x_12; size_t x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_3, x_12);
x_3 = x_13;
goto _start;
}
else
{
uint8_t x_15; 
x_15 = lean_unbox(x_6);
return x_15;
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_4, x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_10 = lean_array_uget(x_3, x_4);
lean_inc(x_1);
x_11 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3(x_1, x_2, x_10, x_6, x_7, x_8);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_4, x_15);
x_4 = x_16;
x_6 = x_12;
x_8 = x_13;
goto _start;
}
else
{
lean_object* x_18; 
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set(x_18, 1, x_8);
return x_18;
}
}
}
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3_spec__4___redArg___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_2, x_5);
if (x_6 == 0)
{
lean_dec(x_5);
return x_3;
}
else
{
if (x_6 == 0)
{
lean_dec(x_5);
return x_3;
}
else
{
size_t x_7; size_t x_8; uint8_t x_9; 
x_7 = lean_usize_of_nat(x_2);
x_8 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_9 = l_Array_anyMUnsafe_any___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__0(x_4, x_1, x_7, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3_spec__4___redArg___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_15; 
x_15 = lean_usize_dec_eq(x_4, x_5);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_16) == 0)
{
x_8 = x_6;
x_9 = x_7;
goto block_14;
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; uint8_t x_23; lean_object* x_24; lean_object* x_30; uint8_t x_36; lean_object* x_37; lean_object* x_44; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_67; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
lean_inc(x_1);
x_67 = l_Nat_anyTR_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__1___redArg(x_17, x_6, x_1, x_1);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; lean_object* x_110; uint8_t x_111; 
x_68 = lean_unsigned_to_nat(0u);
x_110 = lean_array_get_size(x_2);
x_111 = lean_nat_dec_lt(x_68, x_110);
if (x_111 == 0)
{
lean_dec(x_110);
x_69 = x_67;
goto block_109;
}
else
{
if (x_111 == 0)
{
lean_dec(x_110);
x_69 = x_67;
goto block_109;
}
else
{
size_t x_112; size_t x_113; uint8_t x_114; 
x_112 = lean_usize_of_nat(x_68);
x_113 = lean_usize_of_nat(x_110);
lean_dec(x_110);
x_114 = l_Array_anyMUnsafe_any___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__2(x_17, x_2, x_112, x_113);
x_69 = x_114;
goto block_109;
}
}
block_109:
{
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_box(x_69);
lean_inc(x_6);
x_71 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3_spec__4___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_71, 0, x_6);
lean_closure_set(x_71, 1, x_68);
lean_closure_set(x_71, 2, x_70);
x_72 = lean_box(x_69);
x_73 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3_spec__4___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_73, 0, x_72);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_74 = lean_ctor_get(x_17, 3);
lean_inc(x_74);
x_75 = lean_ctor_get(x_7, 0);
lean_inc(x_75);
x_76 = lean_unsigned_to_nat(8u);
x_77 = lean_unsigned_to_nat(2u);
x_78 = lean_nat_shiftl(x_76, x_77);
x_79 = lean_unsigned_to_nat(3u);
x_80 = lean_nat_div(x_78, x_79);
lean_dec(x_78);
x_81 = l_Nat_nextPowerOfTwo(x_80);
lean_dec(x_80);
x_82 = lean_box(0);
x_83 = lean_mk_array(x_81, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_68);
lean_ctor_set(x_84, 1, x_83);
lean_inc(x_75);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_75);
x_86 = l_Lean_Expr_hasFVar(x_74);
if (x_86 == 0)
{
uint8_t x_87; 
x_87 = l_Lean_Expr_hasMVar(x_74);
if (x_87 == 0)
{
lean_dec(x_85);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
x_23 = x_87;
x_24 = x_75;
goto block_29;
}
else
{
lean_object* x_88; 
lean_dec(x_75);
x_88 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_71, x_73, x_74, x_85);
x_30 = x_88;
goto block_35;
}
}
else
{
lean_object* x_89; 
lean_dec(x_75);
x_89 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_71, x_73, x_74, x_85);
x_30 = x_89;
goto block_35;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_90 = lean_ctor_get(x_17, 3);
lean_inc(x_90);
x_91 = lean_ctor_get(x_17, 4);
lean_inc(x_91);
x_92 = lean_ctor_get(x_7, 0);
lean_inc(x_92);
x_93 = lean_unsigned_to_nat(8u);
x_94 = lean_unsigned_to_nat(2u);
x_95 = lean_nat_shiftl(x_93, x_94);
x_96 = lean_unsigned_to_nat(3u);
x_97 = lean_nat_div(x_95, x_96);
lean_dec(x_95);
x_98 = l_Nat_nextPowerOfTwo(x_97);
lean_dec(x_97);
x_99 = lean_box(0);
x_100 = lean_mk_array(x_98, x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_68);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_92);
x_103 = l_Lean_Expr_hasFVar(x_90);
if (x_103 == 0)
{
uint8_t x_104; 
x_104 = l_Lean_Expr_hasMVar(x_90);
if (x_104 == 0)
{
lean_dec(x_90);
x_49 = x_73;
x_50 = x_71;
x_51 = x_91;
x_52 = x_104;
x_53 = x_102;
goto block_58;
}
else
{
lean_object* x_105; 
lean_inc(x_73);
lean_inc(x_71);
x_105 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_71, x_73, x_90, x_102);
x_59 = x_73;
x_60 = x_71;
x_61 = x_91;
x_62 = x_105;
goto block_66;
}
}
else
{
lean_object* x_106; 
lean_inc(x_73);
lean_inc(x_71);
x_106 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_71, x_73, x_90, x_102);
x_59 = x_73;
x_60 = x_71;
x_61 = x_91;
x_62 = x_106;
goto block_66;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = l_Lean_LocalDecl_toExpr(x_17);
x_108 = lean_array_push(x_6, x_107);
x_8 = x_108;
x_9 = x_7;
goto block_14;
}
}
}
else
{
lean_dec(x_17);
x_8 = x_6;
x_9 = x_7;
goto block_14;
}
block_22:
{
if (x_18 == 0)
{
lean_dec(x_17);
x_8 = x_6;
x_9 = x_19;
goto block_14;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Lean_LocalDecl_toExpr(x_17);
x_21 = lean_array_push(x_6, x_20);
x_8 = x_21;
x_9 = x_19;
goto block_14;
}
}
block_29:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_7, 2);
lean_inc(x_26);
x_27 = lean_ctor_get(x_7, 3);
lean_inc(x_27);
lean_dec(x_7);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_25);
lean_ctor_set(x_28, 2, x_26);
lean_ctor_set(x_28, 3, x_27);
x_18 = x_23;
x_19 = x_28;
goto block_22;
}
block_35:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_unbox(x_32);
lean_dec(x_32);
x_23 = x_34;
x_24 = x_33;
goto block_29;
}
block_43:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_ctor_get(x_7, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_7, 2);
lean_inc(x_40);
x_41 = lean_ctor_get(x_7, 3);
lean_inc(x_41);
lean_dec(x_7);
x_42 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_39);
lean_ctor_set(x_42, 2, x_40);
lean_ctor_set(x_42, 3, x_41);
x_18 = x_36;
x_19 = x_42;
goto block_22;
}
block_48:
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_unbox(x_45);
lean_dec(x_45);
x_36 = x_47;
x_37 = x_46;
goto block_43;
}
block_58:
{
if (x_52 == 0)
{
uint8_t x_54; 
x_54 = l_Lean_Expr_hasFVar(x_51);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = l_Lean_Expr_hasMVar(x_51);
if (x_55 == 0)
{
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
x_36 = x_55;
x_37 = x_53;
goto block_43;
}
else
{
lean_object* x_56; 
x_56 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_50, x_49, x_51, x_53);
x_44 = x_56;
goto block_48;
}
}
else
{
lean_object* x_57; 
x_57 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_50, x_49, x_51, x_53);
x_44 = x_57;
goto block_48;
}
}
else
{
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
x_36 = x_52;
x_37 = x_53;
goto block_43;
}
}
block_66:
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_unbox(x_63);
lean_dec(x_63);
x_49 = x_59;
x_50 = x_60;
x_51 = x_61;
x_52 = x_65;
x_53 = x_64;
goto block_58;
}
}
}
else
{
lean_object* x_115; 
lean_dec(x_1);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_6);
lean_ctor_set(x_115, 1, x_7);
return x_115;
}
block_14:
{
lean_object* x_10; size_t x_11; size_t x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_4, x_11);
x_4 = x_12;
x_6 = x_8;
x_7 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_get_size(x_7);
x_10 = lean_nat_dec_lt(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_9, x_9);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_6);
return x_13;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_usize_of_nat(x_8);
x_15 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_16 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3_spec__3(x_1, x_2, x_7, x_14, x_15, x_4, x_5, x_6);
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_get_size(x_17);
x_20 = lean_nat_dec_lt(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_19);
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_6);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_le(x_19, x_19);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_19);
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; 
x_24 = lean_usize_of_nat(x_18);
x_25 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_26 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3_spec__4___redArg(x_1, x_2, x_17, x_24, x_25, x_4, x_6);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_9; lean_object* x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = l_Lean_instInhabitedPersistentArrayNode(lean_box(0));
x_11 = lean_usize_shift_right(x_4, x_5);
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get(x_10, x_9, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_shift_left(x_15, x_5);
x_17 = lean_usize_sub(x_16, x_15);
x_18 = lean_usize_land(x_4, x_17);
x_19 = lean_unsigned_to_nat(5u);
x_20 = lean_usize_of_nat(x_19);
x_21 = lean_usize_sub(x_5, x_20);
lean_inc(x_1);
x_22 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3(x_1, x_2, x_13, x_18, x_21, x_6, x_7, x_8);
lean_dec(x_13);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
x_25 = lean_nat_add(x_12, x_14);
lean_dec(x_12);
x_26 = lean_array_get_size(x_9);
x_27 = lean_nat_dec_lt(x_25, x_26);
if (x_27 == 0)
{
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_1);
return x_22;
}
else
{
uint8_t x_28; 
x_28 = lean_nat_dec_le(x_26, x_26);
if (x_28 == 0)
{
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_1);
return x_22;
}
else
{
size_t x_29; size_t x_30; lean_object* x_31; 
lean_dec(x_22);
x_29 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_30 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_31 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3_spec__3(x_1, x_2, x_9, x_29, x_30, x_23, x_7, x_24);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_3, 0);
x_33 = lean_usize_to_nat(x_4);
x_34 = lean_array_get_size(x_32);
x_35 = lean_nat_dec_lt(x_33, x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_1);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_6);
lean_ctor_set(x_36, 1, x_8);
return x_36;
}
else
{
uint8_t x_37; 
x_37 = lean_nat_dec_le(x_34, x_34);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_1);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_6);
lean_ctor_set(x_38, 1, x_8);
return x_38;
}
else
{
size_t x_39; size_t x_40; lean_object* x_41; 
x_39 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_40 = lean_usize_of_nat(x_34);
lean_dec(x_34);
x_41 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3_spec__4___redArg(x_1, x_2, x_32, x_39, x_40, x_6, x_8);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_5, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_3, 3);
x_11 = lean_nat_dec_le(x_10, x_5);
if (x_11 == 0)
{
lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_usize_of_nat(x_5);
x_14 = lean_ctor_get_usize(x_3, 4);
lean_inc(x_1);
x_15 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3(x_1, x_2, x_12, x_13, x_14, x_4, x_6, x_7);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 1);
x_19 = lean_array_get_size(x_18);
x_20 = lean_nat_dec_lt(x_8, x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_1);
return x_15;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_19, x_19);
if (x_21 == 0)
{
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_1);
return x_15;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; 
lean_dec(x_15);
x_22 = lean_usize_of_nat(x_8);
x_23 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_24 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3_spec__4___redArg(x_1, x_2, x_18, x_22, x_23, x_16, x_17);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_3, 1);
x_26 = lean_nat_sub(x_5, x_10);
x_27 = lean_array_get_size(x_25);
x_28 = lean_nat_dec_lt(x_26, x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_1);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_4);
lean_ctor_set(x_29, 1, x_7);
return x_29;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_27, x_27);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_1);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_4);
lean_ctor_set(x_31, 1, x_7);
return x_31;
}
else
{
size_t x_32; size_t x_33; lean_object* x_34; 
x_32 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_33 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_34 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3_spec__4___redArg(x_1, x_2, x_25, x_32, x_33, x_4, x_7);
return x_34;
}
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_35 = lean_ctor_get(x_3, 0);
lean_inc(x_1);
x_36 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3(x_1, x_2, x_35, x_4, x_6, x_7);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_3, 1);
x_40 = lean_array_get_size(x_39);
x_41 = lean_nat_dec_lt(x_8, x_40);
if (x_41 == 0)
{
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_1);
return x_36;
}
else
{
uint8_t x_42; 
x_42 = lean_nat_dec_le(x_40, x_40);
if (x_42 == 0)
{
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_1);
return x_36;
}
else
{
size_t x_43; size_t x_44; lean_object* x_45; 
lean_dec(x_36);
x_43 = lean_usize_of_nat(x_8);
x_44 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_45 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3_spec__4___redArg(x_1, x_2, x_39, x_43, x_44, x_37, x_38);
return x_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 1);
x_9 = l_Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__9___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_13; uint8_t x_19; lean_object* x_20; lean_object* x_37; lean_object* x_42; lean_object* x_43; 
x_42 = lean_alloc_closure((void*)(l_Lean_exprDependsOn___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_42, 0, x_2);
x_43 = lean_alloc_closure((void*)(l_Lean_exprDependsOn___redArg___lam__1___boxed), 1, 0);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_44 = lean_ctor_get(x_1, 3);
lean_inc(x_44);
lean_dec(x_1);
x_45 = lean_ctor_get(x_3, 0);
lean_inc(x_45);
x_46 = lean_unsigned_to_nat(8u);
x_47 = lean_unsigned_to_nat(0u);
x_48 = lean_unsigned_to_nat(2u);
x_49 = lean_nat_shiftl(x_46, x_48);
x_50 = lean_unsigned_to_nat(3u);
x_51 = lean_nat_div(x_49, x_50);
lean_dec(x_49);
x_52 = l_Nat_nextPowerOfTwo(x_51);
lean_dec(x_51);
x_53 = lean_box(0);
x_54 = lean_mk_array(x_52, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_47);
lean_ctor_set(x_55, 1, x_54);
lean_inc(x_45);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_45);
x_57 = l_Lean_Expr_hasFVar(x_44);
if (x_57 == 0)
{
uint8_t x_58; 
x_58 = l_Lean_Expr_hasMVar(x_44);
if (x_58 == 0)
{
lean_dec(x_56);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
x_4 = x_58;
x_5 = x_45;
goto block_12;
}
else
{
lean_object* x_59; 
lean_dec(x_45);
x_59 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_42, x_43, x_44, x_56);
x_13 = x_59;
goto block_18;
}
}
else
{
lean_object* x_60; 
lean_dec(x_45);
x_60 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_42, x_43, x_44, x_56);
x_13 = x_60;
goto block_18;
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_70; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_61 = lean_ctor_get(x_1, 3);
lean_inc(x_61);
x_62 = lean_ctor_get(x_1, 4);
lean_inc(x_62);
lean_dec(x_1);
x_75 = lean_ctor_get(x_3, 0);
lean_inc(x_75);
x_76 = lean_unsigned_to_nat(8u);
x_77 = lean_unsigned_to_nat(0u);
x_78 = lean_unsigned_to_nat(2u);
x_79 = lean_nat_shiftl(x_76, x_78);
x_80 = lean_unsigned_to_nat(3u);
x_81 = lean_nat_div(x_79, x_80);
lean_dec(x_79);
x_82 = l_Nat_nextPowerOfTwo(x_81);
lean_dec(x_81);
x_83 = lean_box(0);
x_84 = lean_mk_array(x_82, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_77);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_75);
x_87 = l_Lean_Expr_hasFVar(x_61);
if (x_87 == 0)
{
uint8_t x_88; 
x_88 = l_Lean_Expr_hasMVar(x_61);
if (x_88 == 0)
{
lean_dec(x_61);
x_63 = x_88;
x_64 = x_86;
goto block_69;
}
else
{
lean_object* x_89; 
lean_inc(x_43);
lean_inc(x_42);
x_89 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_42, x_43, x_61, x_86);
x_70 = x_89;
goto block_74;
}
}
else
{
lean_object* x_90; 
lean_inc(x_43);
lean_inc(x_42);
x_90 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_42, x_43, x_61, x_86);
x_70 = x_90;
goto block_74;
}
block_69:
{
if (x_63 == 0)
{
uint8_t x_65; 
x_65 = l_Lean_Expr_hasFVar(x_62);
if (x_65 == 0)
{
uint8_t x_66; 
x_66 = l_Lean_Expr_hasMVar(x_62);
if (x_66 == 0)
{
lean_dec(x_62);
lean_dec(x_43);
lean_dec(x_42);
x_19 = x_66;
x_20 = x_64;
goto block_36;
}
else
{
lean_object* x_67; 
x_67 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_42, x_43, x_62, x_64);
x_37 = x_67;
goto block_41;
}
}
else
{
lean_object* x_68; 
x_68 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_42, x_43, x_62, x_64);
x_37 = x_68;
goto block_41;
}
}
else
{
lean_dec(x_62);
lean_dec(x_43);
lean_dec(x_42);
x_19 = x_63;
x_20 = x_64;
goto block_36;
}
}
block_74:
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_unbox(x_71);
lean_dec(x_71);
x_63 = x_73;
x_64 = x_72;
goto block_69;
}
}
block_12:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 3);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_7);
lean_ctor_set(x_9, 3, x_8);
x_10 = lean_box(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
block_18:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unbox(x_15);
lean_dec(x_15);
x_4 = x_17;
x_5 = x_16;
goto block_12;
}
block_36:
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_20, 1);
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_3, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_3, 3);
lean_inc(x_26);
lean_dec(x_3);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_25);
lean_ctor_set(x_27, 3, x_26);
x_28 = lean_box(x_19);
lean_ctor_set(x_20, 1, x_27);
lean_ctor_set(x_20, 0, x_28);
return x_20;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_dec(x_20);
x_30 = lean_ctor_get(x_3, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_3, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_3, 3);
lean_inc(x_32);
lean_dec(x_3);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_30);
lean_ctor_set(x_33, 2, x_31);
lean_ctor_set(x_33, 3, x_32);
x_34 = lean_box(x_19);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
block_41:
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_unbox(x_38);
lean_dec(x_38);
x_19 = x_40;
x_20 = x_39;
goto block_36;
}
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_localDeclDependsOn___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__9___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Nat_forM_loop___at___Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__10_spec__10___redArg___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__10_spec__10___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_6, x_10);
if (x_11 == 1)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_6, x_14);
lean_dec(x_6);
x_16 = lean_nat_sub(x_5, x_15);
x_17 = lean_nat_sub(x_16, x_14);
lean_dec(x_16);
x_18 = lean_array_fget(x_1, x_17);
lean_dec(x_17);
lean_inc(x_2);
x_19 = l_Lean_LocalContext_getFVar_x21(x_2, x_18);
lean_dec(x_18);
x_20 = l_Lean_Expr_fvarId_x21(x_3);
lean_inc(x_19);
x_21 = l_Lean_localDeclDependsOn___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__9___redArg(x_19, x_20, x_8);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_19);
lean_dec(x_9);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_6 = x_15;
x_8 = x_24;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_37; 
lean_dec(x_15);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_27 = x_21;
} else {
 lean_dec_ref(x_21);
 x_27 = lean_box(0);
}
x_28 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
x_29 = lean_box(x_28);
x_30 = lean_alloc_closure((void*)(l_Nat_forM_loop___at___Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__10_spec__10___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_30, 0, x_29);
x_31 = lean_ctor_get(x_26, 0);
lean_inc(x_31);
x_37 = lean_ctor_get(x_19, 2);
lean_inc(x_37);
lean_dec(x_19);
x_32 = x_37;
goto block_36;
block_36:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = l_Lean_Name_toString(x_32, x_4, x_30);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_2);
lean_ctor_set(x_34, 2, x_1);
lean_ctor_set(x_34, 3, x_33);
if (lean_is_scalar(x_27)) {
 x_35 = lean_alloc_ctor(1, 2, 0);
} else {
 x_35 = x_27;
 lean_ctor_set_tag(x_35, 1);
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_26);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__10_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_forM_loop___at___Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__10_spec__10___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__10___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_6, x_10);
if (x_11 == 1)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_6, x_14);
x_16 = lean_nat_sub(x_5, x_15);
x_17 = lean_nat_sub(x_16, x_14);
lean_dec(x_16);
x_18 = lean_array_fget(x_1, x_17);
lean_dec(x_17);
lean_inc(x_2);
x_19 = l_Lean_LocalContext_getFVar_x21(x_2, x_18);
lean_dec(x_18);
x_20 = l_Lean_Expr_fvarId_x21(x_3);
lean_inc(x_19);
x_21 = l_Lean_localDeclDependsOn___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__9___redArg(x_19, x_20, x_8);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_19);
lean_dec(x_9);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = l_Nat_forM_loop___at___Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__10_spec__10___redArg(x_1, x_2, x_3, x_4, x_5, x_15, x_7, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_37; 
lean_dec(x_15);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_27 = x_21;
} else {
 lean_dec_ref(x_21);
 x_27 = lean_box(0);
}
x_28 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
x_29 = lean_box(x_28);
x_30 = lean_alloc_closure((void*)(l_Nat_forM_loop___at___Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__10_spec__10___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_30, 0, x_29);
x_31 = lean_ctor_get(x_26, 0);
lean_inc(x_31);
x_37 = lean_ctor_get(x_19, 2);
lean_inc(x_37);
lean_dec(x_19);
x_32 = x_37;
goto block_36;
block_36:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = l_Lean_Name_toString(x_32, x_4, x_30);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_2);
lean_ctor_set(x_34, 2, x_1);
lean_ctor_set(x_34, 3, x_33);
if (lean_is_scalar(x_27)) {
 x_35 = lean_alloc_ctor(1, 2, 0);
} else {
 x_35 = x_27;
 lean_ctor_set_tag(x_35, 1);
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_26);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__10___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__12_spec__12___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_5, x_8);
if (x_9 == 1)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_5, x_12);
lean_dec(x_5);
x_14 = lean_nat_sub(x_4, x_13);
x_15 = lean_nat_sub(x_14, x_12);
lean_dec(x_14);
x_16 = lean_array_fget(x_1, x_15);
lean_inc(x_2);
lean_inc(x_1);
x_17 = l_Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__10___redArg(x_1, x_2, x_16, x_3, x_15, x_15, x_6, x_7);
lean_dec(x_15);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_5 = x_13;
x_7 = x_18;
goto _start;
}
else
{
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__12_spec__12(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Nat_forM_loop___at___Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__12_spec__12___redArg(x_1, x_2, x_3, x_4, x_5, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__12___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_5, x_8);
if (x_9 == 1)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_5, x_12);
x_14 = lean_nat_sub(x_4, x_13);
x_15 = lean_nat_sub(x_14, x_12);
lean_dec(x_14);
x_16 = lean_array_fget(x_1, x_15);
lean_inc(x_2);
lean_inc(x_1);
x_17 = l_Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__10___redArg(x_1, x_2, x_16, x_3, x_15, x_15, x_6, x_7);
lean_dec(x_15);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Nat_forM_loop___at___Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__12_spec__12___redArg(x_1, x_2, x_3, x_4, x_13, x_6, x_18);
return x_19;
}
else
{
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__12(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__12___redArg(x_1, x_2, x_3, x_4, x_5, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_collectForwardDeps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_23; uint8_t x_24; 
x_13 = lean_array_get_size(x_2);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_eq(x_13, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = l_Lean_MetavarContext_MkBinding_preserveOrder(x_3, x_4);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_26);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_14 = x_3;
x_15 = x_28;
goto block_22;
}
else
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_unbox(x_26);
lean_dec(x_26);
lean_inc(x_1);
lean_inc(x_2);
x_31 = l_Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__12___redArg(x_2, x_1, x_30, x_13, x_13, x_3, x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_14 = x_3;
x_15 = x_32;
goto block_22;
}
else
{
uint8_t x_33; 
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_31);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
else
{
lean_object* x_37; 
lean_dec(x_13);
lean_dec(x_1);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_2);
lean_ctor_set(x_37, 1, x_4);
return x_37;
}
block_12:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_2);
lean_inc(x_1);
x_8 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_getLocalDeclWithSmallestIdx(x_1, x_2);
x_9 = lean_array_get_size(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3(x_9, x_2, x_1, x_7, x_10, x_6, x_5);
lean_dec(x_10);
lean_dec(x_1);
lean_dec(x_2);
return x_11;
}
block_22:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = l_Lean_MetavarContext_MkBinding_preserveOrder(x_14, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_mk_empty_array_with_capacity(x_13);
lean_dec(x_13);
x_5 = x_19;
x_6 = x_14;
x_7 = x_20;
goto block_12;
}
else
{
lean_object* x_21; 
lean_dec(x_13);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
lean_inc(x_2);
x_5 = x_21;
x_6 = x_14;
x_7 = x_2;
goto block_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__0(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Nat_anyTR_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Nat_anyTR_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__1___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_anyTR_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Nat_anyTR_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__2(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3_spec__3(x_1, x_2, x_3, x_9, x_10, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3_spec__4___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3_spec__4___redArg___lam__0(x_1, x_2, x_5, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3_spec__4___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3_spec__4___redArg___lam__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3_spec__4___redArg(x_1, x_2, x_3, x_8, x_9, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3_spec__4(x_1, x_2, x_3, x_9, x_10, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3_spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3_spec__3(x_1, x_2, x_3, x_9, x_10, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_LocalContext_foldlM___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_localDeclDependsOn___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__9(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__10_spec__10___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Nat_forM_loop___at___Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__10_spec__10___redArg___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__10_spec__10___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l_Nat_forM_loop___at___Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__10_spec__10___redArg(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__10_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Nat_forM_loop___at___Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__10_spec__10(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__10___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l_Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__10___redArg(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__10(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__12_spec__12___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = l_Nat_forM_loop___at___Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__12_spec__12___redArg(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__12_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Nat_forM_loop___at___Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__12_spec__12(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__12___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = l_Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__12___redArg(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Nat_forM_loop___at___Lean_MetavarContext_MkBinding_collectForwardDeps_spec__12(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_collectForwardDeps___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MetavarContext_MkBinding_collectForwardDeps(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_MetavarContext_MkBinding_reduceLocalContext_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_usize_of_nat(x_6);
x_8 = lean_usize_sub(x_2, x_7);
x_9 = lean_array_uget(x_1, x_8);
x_10 = l_Lean_Expr_isFVar(x_9);
if (x_10 == 0)
{
lean_dec(x_9);
x_2 = x_8;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Expr_fvarId_x21(x_9);
lean_dec(x_9);
x_13 = lean_local_ctx_erase(x_4, x_12);
x_2 = x_8;
x_4 = x_13;
goto _start;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_reduceLocalContext(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec(x_3);
return x_1;
}
else
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_7 = lean_usize_of_nat(x_4);
x_8 = l_Array_foldrMUnsafe_fold___at___Lean_MetavarContext_MkBinding_reduceLocalContext_spec__0(x_2, x_6, x_7, x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_MetavarContext_MkBinding_reduceLocalContext_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldrMUnsafe_fold___at___Lean_MetavarContext_MkBinding_reduceLocalContext_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_reduceLocalContext___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MetavarContext_MkBinding_reduceLocalContext(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_getInScope_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_3, x_4);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_uget(x_2, x_3);
x_14 = l_Lean_Expr_isFVar(x_13);
if (x_14 == 0)
{
lean_dec(x_13);
x_6 = x_5;
goto block_11;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Expr_fvarId_x21(x_13);
lean_inc(x_1);
x_16 = l_Lean_LocalContext_contains(x_1, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_dec(x_13);
x_6 = x_5;
goto block_11;
}
else
{
lean_object* x_17; 
x_17 = lean_array_push(x_5, x_13);
x_6 = x_17;
goto block_11;
}
}
}
else
{
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
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_getInScope(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_4;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_5);
if (x_7 == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_4;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_usize_of_nat(x_3);
x_9 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_10 = l_Array_foldlMUnsafe_fold___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_getInScope_spec__0(x_1, x_2, x_8, x_9, x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_getInScope_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_getInScope_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_getInScope___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_getInScope(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_withFreshCache___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
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
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_5);
lean_ctor_set(x_17, 2, x_6);
lean_ctor_set(x_17, 3, x_16);
x_18 = lean_apply_2(x_1, x_2, x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_18, 1);
x_21 = lean_ctor_get(x_3, 3);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 2);
lean_inc(x_24);
lean_dec(x_20);
lean_inc(x_21);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_24);
lean_ctor_set(x_25, 3, x_21);
lean_ctor_set(x_18, 1, x_25);
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
x_28 = lean_ctor_get(x_3, 3);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_27, 2);
lean_inc(x_31);
lean_dec(x_27);
lean_inc(x_28);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_31);
lean_ctor_set(x_32, 3, x_28);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_withFreshCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 2);
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
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_6);
lean_ctor_set(x_18, 2, x_7);
lean_ctor_set(x_18, 3, x_17);
x_19 = lean_apply_2(x_2, x_3, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_19, 1);
x_22 = lean_ctor_get(x_4, 3);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 2);
lean_inc(x_25);
lean_dec(x_21);
lean_inc(x_22);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_25);
lean_ctor_set(x_26, 3, x_22);
lean_ctor_set(x_19, 1, x_26);
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_ctor_get(x_4, 3);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_28, 2);
lean_inc(x_32);
lean_dec(x_28);
lean_inc(x_29);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set(x_33, 3, x_29);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_withFreshCache___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_withFreshCache___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_withFreshCache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_withFreshCache(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkMVarApp_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_4, x_5);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_uget(x_3, x_4);
x_15 = l_Lean_Expr_isFVar(x_14);
if (x_15 == 0)
{
lean_dec(x_14);
x_7 = x_6;
goto block_12;
}
else
{
lean_object* x_16; 
x_16 = lean_box(x_1);
if (lean_obj_tag(x_16) == 2)
{
lean_object* x_17; 
x_17 = l_Lean_Expr_app___override(x_6, x_14);
x_7 = x_17;
goto block_12;
}
else
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_16);
lean_inc(x_2);
x_18 = l_Lean_LocalContext_getFVar_x21(x_2, x_14);
x_19 = l_Lean_LocalDecl_isLet(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = l_Lean_Expr_app___override(x_6, x_14);
x_7 = x_20;
goto block_12;
}
else
{
lean_dec(x_14);
x_7 = x_6;
goto block_12;
}
}
}
}
else
{
lean_dec(x_2);
return x_6;
}
block_12:
{
lean_object* x_8; size_t x_9; size_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_add(x_4, x_9);
x_4 = x_10;
x_6 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkMVarApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_5, x_6);
if (x_7 == 0)
{
lean_dec(x_6);
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_6, x_6);
if (x_8 == 0)
{
lean_dec(x_6);
lean_dec(x_1);
return x_2;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_usize_of_nat(x_5);
x_10 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_11 = l_Array_foldlMUnsafe_fold___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkMVarApp_spec__0(x_4, x_1, x_3, x_9, x_10, x_2);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkMVarApp_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_Array_foldlMUnsafe_fold___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkMVarApp_spec__0(x_7, x_2, x_3, x_8, x_9, x_6);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkMVarApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkMVarApp(x_1, x_2, x_3, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkAuxMVarType_abstractRangeAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elim(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_expr_abstract_range(x_8, x_2, x_1);
lean_dec(x_8);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
x_12 = lean_expr_abstract_range(x_10, x_2, x_1);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elim_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_array_set(x_3, x_4, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_4, x_10);
lean_dec(x_4);
x_2 = x_7;
x_3 = x_9;
x_4 = x_11;
goto _start;
}
else
{
lean_object* x_13; 
lean_dec(x_4);
x_13 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp(x_1, x_2, x_3, x_5, x_6);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_mk_empty_array_with_capacity(x_5);
x_7 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp(x_1, x_2, x_6, x_3, x_4);
return x_7;
}
case 5:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_box(0);
x_9 = l_Lean_Expr_sort___override(x_8);
x_10 = l_Lean_Expr_getAppNumArgs(x_2);
lean_inc(x_10);
x_11 = lean_mk_array(x_10, x_9);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_10, x_12);
lean_dec(x_10);
x_14 = l_Lean_Expr_withAppAux___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elim_spec__0(x_1, x_2, x_11, x_13, x_3, x_4);
return x_14;
}
case 6:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 2);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
lean_inc(x_3);
lean_inc(x_16);
x_19 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit(x_1, x_16, x_3, x_4);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_17);
x_22 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit(x_1, x_17, x_3, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
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
x_26 = l_Lean_Expr_lam___override(x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_26) == 6)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; size_t x_39; size_t x_40; uint8_t x_41; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 2);
lean_inc(x_29);
x_30 = lean_ctor_get_uint8(x_26, sizeof(void*)*3 + 8);
x_39 = lean_ptr_addr(x_28);
lean_dec(x_28);
x_40 = lean_ptr_addr(x_20);
x_41 = lean_usize_dec_eq(x_39, x_40);
if (x_41 == 0)
{
lean_dec(x_29);
x_31 = x_41;
goto block_38;
}
else
{
size_t x_42; size_t x_43; uint8_t x_44; 
x_42 = lean_ptr_addr(x_29);
lean_dec(x_29);
x_43 = lean_ptr_addr(x_23);
x_44 = lean_usize_dec_eq(x_42, x_43);
x_31 = x_44;
goto block_38;
}
block_38:
{
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_26);
x_32 = l_Lean_Expr_lam___override(x_27, x_20, x_23, x_18);
if (lean_is_scalar(x_25)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_25;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_24);
return x_33;
}
else
{
uint8_t x_34; 
x_34 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_30, x_18);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_26);
x_35 = l_Lean_Expr_lam___override(x_27, x_20, x_23, x_18);
if (lean_is_scalar(x_25)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_25;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_24);
return x_36;
}
else
{
lean_object* x_37; 
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_20);
if (lean_is_scalar(x_25)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_25;
}
lean_ctor_set(x_37, 0, x_26);
lean_ctor_set(x_37, 1, x_24);
return x_37;
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_20);
x_45 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_46 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateLambda!Impl", 48, 48);
x_47 = lean_unsigned_to_nat(1848u);
x_48 = lean_unsigned_to_nat(19u);
x_49 = lean_mk_string_unchecked("lambda expected", 15, 15);
x_50 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_45, x_46, x_47, x_48, x_49);
lean_dec(x_49);
lean_dec(x_46);
lean_dec(x_45);
x_51 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_50);
if (lean_is_scalar(x_25)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_25;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_24);
return x_52;
}
}
else
{
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
return x_22;
}
}
else
{
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_3);
return x_19;
}
}
case 7:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_2, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_2, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_2, 2);
lean_inc(x_55);
x_56 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
lean_inc(x_3);
lean_inc(x_54);
x_57 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit(x_1, x_54, x_3, x_4);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_inc(x_55);
x_60 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit(x_1, x_55, x_3, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
x_64 = l_Lean_Expr_forallE___override(x_53, x_54, x_55, x_56);
if (lean_obj_tag(x_64) == 7)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_69; size_t x_77; size_t x_78; uint8_t x_79; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_64, 2);
lean_inc(x_67);
x_68 = lean_ctor_get_uint8(x_64, sizeof(void*)*3 + 8);
x_77 = lean_ptr_addr(x_66);
lean_dec(x_66);
x_78 = lean_ptr_addr(x_58);
x_79 = lean_usize_dec_eq(x_77, x_78);
if (x_79 == 0)
{
lean_dec(x_67);
x_69 = x_79;
goto block_76;
}
else
{
size_t x_80; size_t x_81; uint8_t x_82; 
x_80 = lean_ptr_addr(x_67);
lean_dec(x_67);
x_81 = lean_ptr_addr(x_61);
x_82 = lean_usize_dec_eq(x_80, x_81);
x_69 = x_82;
goto block_76;
}
block_76:
{
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_64);
x_70 = l_Lean_Expr_forallE___override(x_65, x_58, x_61, x_56);
if (lean_is_scalar(x_63)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_63;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_62);
return x_71;
}
else
{
uint8_t x_72; 
x_72 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_68, x_56);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_64);
x_73 = l_Lean_Expr_forallE___override(x_65, x_58, x_61, x_56);
if (lean_is_scalar(x_63)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_63;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_62);
return x_74;
}
else
{
lean_object* x_75; 
lean_dec(x_65);
lean_dec(x_61);
lean_dec(x_58);
if (lean_is_scalar(x_63)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_63;
}
lean_ctor_set(x_75, 0, x_64);
lean_ctor_set(x_75, 1, x_62);
return x_75;
}
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_64);
lean_dec(x_61);
lean_dec(x_58);
x_83 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_84 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateForall!Impl", 48, 48);
x_85 = lean_unsigned_to_nat(1828u);
x_86 = lean_unsigned_to_nat(23u);
x_87 = lean_mk_string_unchecked("forall expected", 15, 15);
x_88 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_83, x_84, x_85, x_86, x_87);
lean_dec(x_87);
lean_dec(x_84);
lean_dec(x_83);
x_89 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_88);
if (lean_is_scalar(x_63)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_63;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_62);
return x_90;
}
}
else
{
lean_dec(x_58);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
return x_60;
}
}
else
{
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_3);
return x_57;
}
}
case 8:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; 
x_91 = lean_ctor_get(x_2, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_2, 1);
lean_inc(x_92);
x_93 = lean_ctor_get(x_2, 2);
lean_inc(x_93);
x_94 = lean_ctor_get(x_2, 3);
lean_inc(x_94);
x_95 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 8);
lean_inc(x_3);
lean_inc(x_92);
x_96 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit(x_1, x_92, x_3, x_4);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
lean_inc(x_3);
lean_inc(x_93);
x_99 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit(x_1, x_93, x_3, x_98);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_102 = x_99;
} else {
 lean_dec_ref(x_99);
 x_102 = lean_box(0);
}
lean_inc(x_94);
x_103 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit(x_1, x_94, x_3, x_101);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_110; size_t x_116; size_t x_117; uint8_t x_118; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_106 = x_103;
} else {
 lean_dec_ref(x_103);
 x_106 = lean_box(0);
}
x_116 = lean_ptr_addr(x_92);
lean_dec(x_92);
x_117 = lean_ptr_addr(x_97);
x_118 = lean_usize_dec_eq(x_116, x_117);
if (x_118 == 0)
{
lean_dec(x_93);
x_110 = x_118;
goto block_115;
}
else
{
size_t x_119; size_t x_120; uint8_t x_121; 
x_119 = lean_ptr_addr(x_93);
lean_dec(x_93);
x_120 = lean_ptr_addr(x_100);
x_121 = lean_usize_dec_eq(x_119, x_120);
x_110 = x_121;
goto block_115;
}
block_109:
{
lean_object* x_107; lean_object* x_108; 
x_107 = l_Lean_Expr_letE___override(x_91, x_97, x_100, x_104, x_95);
if (lean_is_scalar(x_106)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_106;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_105);
return x_108;
}
block_115:
{
if (x_110 == 0)
{
lean_dec(x_102);
lean_dec(x_94);
lean_dec(x_2);
goto block_109;
}
else
{
size_t x_111; size_t x_112; uint8_t x_113; 
x_111 = lean_ptr_addr(x_94);
lean_dec(x_94);
x_112 = lean_ptr_addr(x_104);
x_113 = lean_usize_dec_eq(x_111, x_112);
if (x_113 == 0)
{
lean_dec(x_102);
lean_dec(x_2);
goto block_109;
}
else
{
lean_object* x_114; 
lean_dec(x_106);
lean_dec(x_104);
lean_dec(x_100);
lean_dec(x_97);
lean_dec(x_91);
if (lean_is_scalar(x_102)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_102;
}
lean_ctor_set(x_114, 0, x_2);
lean_ctor_set(x_114, 1, x_105);
return x_114;
}
}
}
}
else
{
lean_dec(x_102);
lean_dec(x_100);
lean_dec(x_97);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_2);
return x_103;
}
}
else
{
lean_dec(x_97);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_3);
lean_dec(x_2);
return x_99;
}
}
else
{
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_3);
lean_dec(x_2);
return x_96;
}
}
case 10:
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_2, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_2, 1);
lean_inc(x_123);
lean_inc(x_123);
x_124 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit(x_1, x_123, x_3, x_4);
if (lean_obj_tag(x_124) == 0)
{
uint8_t x_125; 
x_125 = !lean_is_exclusive(x_124);
if (x_125 == 0)
{
lean_object* x_126; size_t x_127; size_t x_128; uint8_t x_129; 
x_126 = lean_ctor_get(x_124, 0);
x_127 = lean_ptr_addr(x_123);
lean_dec(x_123);
x_128 = lean_ptr_addr(x_126);
x_129 = lean_usize_dec_eq(x_127, x_128);
if (x_129 == 0)
{
lean_object* x_130; 
lean_dec(x_2);
x_130 = l_Lean_Expr_mdata___override(x_122, x_126);
lean_ctor_set(x_124, 0, x_130);
return x_124;
}
else
{
lean_dec(x_126);
lean_dec(x_122);
lean_ctor_set(x_124, 0, x_2);
return x_124;
}
}
else
{
lean_object* x_131; lean_object* x_132; size_t x_133; size_t x_134; uint8_t x_135; 
x_131 = lean_ctor_get(x_124, 0);
x_132 = lean_ctor_get(x_124, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_124);
x_133 = lean_ptr_addr(x_123);
lean_dec(x_123);
x_134 = lean_ptr_addr(x_131);
x_135 = lean_usize_dec_eq(x_133, x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_2);
x_136 = l_Lean_Expr_mdata___override(x_122, x_131);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_132);
return x_137;
}
else
{
lean_object* x_138; 
lean_dec(x_131);
lean_dec(x_122);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_2);
lean_ctor_set(x_138, 1, x_132);
return x_138;
}
}
}
else
{
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_2);
return x_124;
}
}
case 11:
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_139 = lean_ctor_get(x_2, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_2, 1);
lean_inc(x_140);
x_141 = lean_ctor_get(x_2, 2);
lean_inc(x_141);
lean_inc(x_141);
x_142 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit(x_1, x_141, x_3, x_4);
if (lean_obj_tag(x_142) == 0)
{
uint8_t x_143; 
x_143 = !lean_is_exclusive(x_142);
if (x_143 == 0)
{
lean_object* x_144; size_t x_145; size_t x_146; uint8_t x_147; 
x_144 = lean_ctor_get(x_142, 0);
x_145 = lean_ptr_addr(x_141);
lean_dec(x_141);
x_146 = lean_ptr_addr(x_144);
x_147 = lean_usize_dec_eq(x_145, x_146);
if (x_147 == 0)
{
lean_object* x_148; 
lean_dec(x_2);
x_148 = l_Lean_Expr_proj___override(x_139, x_140, x_144);
lean_ctor_set(x_142, 0, x_148);
return x_142;
}
else
{
lean_dec(x_144);
lean_dec(x_140);
lean_dec(x_139);
lean_ctor_set(x_142, 0, x_2);
return x_142;
}
}
else
{
lean_object* x_149; lean_object* x_150; size_t x_151; size_t x_152; uint8_t x_153; 
x_149 = lean_ctor_get(x_142, 0);
x_150 = lean_ctor_get(x_142, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_142);
x_151 = lean_ptr_addr(x_141);
lean_dec(x_141);
x_152 = lean_ptr_addr(x_149);
x_153 = lean_usize_dec_eq(x_151, x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_2);
x_154 = l_Lean_Expr_proj___override(x_139, x_140, x_149);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_150);
return x_155;
}
else
{
lean_object* x_156; 
lean_dec(x_149);
lean_dec(x_140);
lean_dec(x_139);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_2);
lean_ctor_set(x_156, 1, x_150);
return x_156;
}
}
}
else
{
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_2);
return x_142;
}
}
default: 
{
lean_object* x_157; 
lean_dec(x_3);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_2);
lean_ctor_set(x_157, 1, x_4);
return x_157;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = l_Lean_MetavarContext_getExprAssignmentCore_x3f(x_3, x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getExprMVarAssignment_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp_spec__0___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_findCore___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_3, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_uget(x_4, x_3);
lean_inc(x_5);
x_10 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit(x_1, x_9, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = lean_array_uset(x_4, x_3, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_add(x_3, x_16);
x_18 = lean_array_uset(x_14, x_3, x_11);
x_3 = x_17;
x_4 = x_18;
x_6 = x_12;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_5);
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
return x_10;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_10);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = l_Lean_getExprMVarAssignment_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp_spec__0___redArg(x_6, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
x_11 = l_Lean_RBNode_findCore___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp_spec__1___redArg(x_10, x_6);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
lean_dec(x_2);
x_12 = lean_box(1);
x_13 = lean_unbox(x_12);
x_14 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar(x_1, x_6, x_3, x_13, x_4, x_9);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
size_t x_26; lean_object* x_27; size_t x_28; lean_object* x_29; 
lean_dec(x_11);
lean_dec(x_6);
x_26 = lean_array_size(x_3);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_usize_of_nat(x_27);
x_29 = l_Array_mapMUnsafe_map___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp_spec__2(x_1, x_26, x_28, x_3, x_4, x_9);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = l_Lean_mkAppN(x_2, x_31);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_29, 0);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_29);
x_35 = l_Lean_mkAppN(x_2, x_33);
lean_dec(x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
return x_29;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_29, 0);
x_39 = lean_ctor_get(x_29, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_29);
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
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_6);
lean_dec(x_2);
x_41 = lean_ctor_get(x_7, 1);
lean_inc(x_41);
lean_dec(x_7);
x_42 = lean_ctor_get(x_8, 0);
lean_inc(x_42);
lean_dec(x_8);
x_43 = l_Lean_Expr_isLambda(x_42);
if (x_43 == 0)
{
x_2 = x_42;
x_5 = x_41;
goto _start;
}
else
{
size_t x_45; lean_object* x_46; size_t x_47; lean_object* x_48; 
x_45 = lean_array_size(x_3);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_usize_of_nat(x_46);
lean_inc(x_4);
x_48 = l_Array_mapMUnsafe_map___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp_spec__2(x_1, x_45, x_47, x_3, x_4, x_41);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Array_reverse(lean_box(0), x_49);
x_52 = lean_box(0);
x_53 = lean_unbox(x_52);
x_54 = lean_unbox(x_52);
x_55 = l_Lean_Expr_betaRev(x_42, x_51, x_53, x_54);
lean_dec(x_51);
x_56 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elim(x_1, x_55, x_4, x_50);
return x_56;
}
else
{
uint8_t x_57; 
lean_dec(x_42);
lean_dec(x_4);
x_57 = !lean_is_exclusive(x_48);
if (x_57 == 0)
{
return x_48;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_48, 0);
x_59 = lean_ctor_get(x_48, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_48);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
}
else
{
lean_object* x_61; 
lean_inc(x_4);
x_61 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit(x_1, x_2, x_4, x_5);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; size_t x_64; lean_object* x_65; size_t x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_array_size(x_3);
x_65 = lean_unsigned_to_nat(0u);
x_66 = lean_usize_of_nat(x_65);
x_67 = l_Array_mapMUnsafe_map___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp_spec__2(x_1, x_64, x_66, x_3, x_4, x_63);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = l_Lean_mkAppN(x_62, x_69);
lean_dec(x_69);
lean_ctor_set(x_67, 0, x_70);
return x_67;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_67, 0);
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_67);
x_73 = l_Lean_mkAppN(x_62, x_71);
lean_dec(x_71);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
else
{
uint8_t x_75; 
lean_dec(x_62);
x_75 = !lean_is_exclusive(x_67);
if (x_75 == 0)
{
return x_67;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_67, 0);
x_77 = lean_ctor_get(x_67, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_67);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_inc(x_3);
x_4 = l_Lean_MetavarContext_getDecl(x_3, x_1);
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_nat_dec_eq(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MVarId_isAssignable___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__0___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_expr_eqv(x_7, x_6);
lean_dec(x_6);
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
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_5 = lean_box(0);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
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
lean_dec(x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_3);
x_17 = l_Lean_PersistentHashMap_insert___at___Lean_assignExp_spec__0___redArg(x_15, x_1, x_16);
x_18 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_8);
lean_ctor_set(x_18, 2, x_9);
lean_ctor_set(x_18, 3, x_10);
lean_ctor_set(x_18, 4, x_11);
lean_ctor_set(x_18, 5, x_12);
lean_ctor_set(x_18, 6, x_13);
lean_ctor_set(x_18, 7, x_14);
lean_ctor_set(x_18, 8, x_17);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_4, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_4, 3);
lean_inc(x_21);
lean_dec(x_4);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set(x_22, 3, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_assignDelayedMVar___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__2___redArg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_4 = lean_box(0);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 4);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 5);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 6);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 7);
lean_inc(x_13);
x_14 = l_Lean_PersistentHashMap_insert___at___Lean_assignExp_spec__0___redArg(x_13, x_1, x_2);
x_15 = lean_ctor_get(x_5, 8);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_7);
lean_ctor_set(x_16, 2, x_8);
lean_ctor_set(x_16, 3, x_9);
lean_ctor_set(x_16, 4, x_10);
lean_ctor_set(x_16, 5, x_11);
lean_ctor_set(x_16, 6, x_12);
lean_ctor_set(x_16, 7, x_14);
lean_ctor_set(x_16, 8, x_15);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_3, 3);
lean_inc(x_19);
lean_dec(x_3);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_18);
lean_ctor_set(x_20, 3, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MVarId_assign___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__3___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__4___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(x_3, x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getDelayedMVarAssignment_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__4___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__5_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = l_Lean_MetavarContext_getDecl(x_15, x_3);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_getInScope(x_17, x_4);
x_19 = lean_usize_dec_eq(x_6, x_7);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; lean_object* x_27; uint8_t x_28; 
x_20 = lean_array_get_size(x_18);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_eq(x_20, x_21);
lean_dec(x_20);
x_23 = lean_array_uget(x_5, x_6);
x_27 = lean_array_get_size(x_1);
x_28 = lean_nat_dec_lt(x_21, x_27);
if (x_28 == 0)
{
lean_dec(x_27);
x_24 = x_22;
goto block_26;
}
else
{
if (x_28 == 0)
{
lean_dec(x_27);
x_24 = x_22;
goto block_26;
}
else
{
size_t x_29; size_t x_30; uint8_t x_31; 
x_29 = lean_usize_of_nat(x_21);
x_30 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_31 = l_Array_anyMUnsafe_any___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__1(x_23, x_1, x_29, x_30);
x_24 = x_31;
goto block_26;
}
}
block_26:
{
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_array_push(x_8, x_23);
x_9 = x_25;
goto block_14;
}
else
{
lean_dec(x_23);
x_9 = x_8;
goto block_14;
}
}
}
else
{
lean_dec(x_18);
lean_dec(x_2);
return x_8;
}
block_14:
{
lean_object* x_10; size_t x_11; size_t x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_6, x_11);
x_6 = x_12;
x_8 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = l_Lean_MetavarContext_getDecl(x_15, x_3);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_getInScope(x_17, x_4);
x_19 = lean_usize_dec_eq(x_6, x_7);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; lean_object* x_27; uint8_t x_28; 
x_20 = lean_array_get_size(x_18);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_eq(x_20, x_21);
lean_dec(x_20);
x_23 = lean_array_uget(x_5, x_6);
x_27 = lean_array_get_size(x_1);
x_28 = lean_nat_dec_lt(x_21, x_27);
if (x_28 == 0)
{
lean_dec(x_27);
x_24 = x_22;
goto block_26;
}
else
{
if (x_28 == 0)
{
lean_dec(x_27);
x_24 = x_22;
goto block_26;
}
else
{
size_t x_29; size_t x_30; uint8_t x_31; 
x_29 = lean_usize_of_nat(x_21);
x_30 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_31 = l_Array_anyMUnsafe_any___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__1(x_23, x_1, x_29, x_30);
x_24 = x_31;
goto block_26;
}
}
block_26:
{
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_array_push(x_8, x_23);
x_9 = x_25;
goto block_14;
}
else
{
lean_dec(x_23);
x_9 = x_8;
goto block_14;
}
}
}
else
{
lean_dec(x_18);
lean_dec(x_2);
return x_8;
}
block_14:
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_6, x_11);
x_13 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__5_spec__5(x_1, x_2, x_3, x_4, x_5, x_12, x_7, x_9);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_mkAppN(x_1, x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; 
x_28 = lean_ctor_get(x_6, 0);
lean_inc(x_28);
x_29 = l_Lean_MetavarContext_getDecl(x_28, x_2);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_inc(x_30);
x_31 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_getInScope(x_30, x_1);
x_32 = lean_array_get_size(x_31);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_nat_dec_eq(x_32, x_33);
lean_dec(x_32);
if (x_34 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_140; 
lean_inc(x_6);
x_108 = l_Lean_MVarId_isAssignable___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__0___redArg(x_2, x_6);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_140 = lean_unbox(x_109);
lean_dec(x_109);
if (x_140 == 0)
{
goto block_139;
}
else
{
if (x_34 == 0)
{
uint8_t x_141; 
x_141 = lean_ctor_get_uint8(x_29, sizeof(void*)*7);
x_111 = x_141;
goto block_136;
}
else
{
goto block_139;
}
}
block_136:
{
size_t x_112; size_t x_113; lean_object* x_114; 
x_112 = lean_array_size(x_3);
x_113 = lean_usize_of_nat(x_33);
lean_inc(x_5);
x_114 = l_Array_mapMUnsafe_map___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp_spec__2(x_1, x_112, x_113, x_3, x_5, x_110);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
lean_inc(x_30);
x_117 = l_Lean_MetavarContext_MkBinding_collectForwardDeps(x_30, x_31, x_5, x_116);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
lean_inc(x_30);
x_120 = l_Lean_MetavarContext_MkBinding_reduceLocalContext(x_30, x_118);
x_121 = lean_ctor_get(x_29, 4);
lean_inc(x_121);
x_122 = lean_array_get_size(x_121);
x_123 = lean_mk_empty_array_with_capacity(x_33);
x_124 = lean_nat_dec_lt(x_33, x_122);
if (x_124 == 0)
{
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_6);
x_73 = x_119;
x_74 = x_118;
x_75 = x_115;
x_76 = x_111;
x_77 = x_120;
x_78 = x_123;
goto block_107;
}
else
{
uint8_t x_125; 
x_125 = lean_nat_dec_le(x_122, x_122);
if (x_125 == 0)
{
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_6);
x_73 = x_119;
x_74 = x_118;
x_75 = x_115;
x_76 = x_111;
x_77 = x_120;
x_78 = x_123;
goto block_107;
}
else
{
size_t x_126; lean_object* x_127; 
x_126 = lean_usize_of_nat(x_122);
lean_dec(x_122);
x_127 = l_Array_foldlMUnsafe_fold___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__5(x_118, x_6, x_2, x_1, x_121, x_113, x_126, x_123);
lean_dec(x_121);
x_73 = x_119;
x_74 = x_118;
x_75 = x_115;
x_76 = x_111;
x_77 = x_120;
x_78 = x_127;
goto block_107;
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_115);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_128 = !lean_is_exclusive(x_117);
if (x_128 == 0)
{
return x_117;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_117, 0);
x_130 = lean_ctor_get(x_117, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_117);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
else
{
uint8_t x_132; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_132 = !lean_is_exclusive(x_114);
if (x_132 == 0)
{
return x_114;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_114, 0);
x_134 = lean_ctor_get(x_114, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_114);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
block_139:
{
lean_object* x_137; uint8_t x_138; 
x_137 = lean_box(2);
x_138 = lean_unbox(x_137);
x_111 = x_138;
goto block_136;
}
}
else
{
size_t x_142; size_t x_143; lean_object* x_144; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
x_142 = lean_array_size(x_3);
x_143 = lean_usize_of_nat(x_33);
x_144 = l_Array_mapMUnsafe_map___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp_spec__2(x_1, x_142, x_143, x_3, x_5, x_6);
if (lean_obj_tag(x_144) == 0)
{
uint8_t x_145; 
x_145 = !lean_is_exclusive(x_144);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_146 = lean_ctor_get(x_144, 0);
x_147 = l_Lean_Expr_mvar___override(x_2);
x_148 = l_Lean_mkAppN(x_147, x_146);
lean_dec(x_146);
x_149 = lean_mk_empty_array_with_capacity(x_33);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
lean_ctor_set(x_144, 0, x_150);
return x_144;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_151 = lean_ctor_get(x_144, 0);
x_152 = lean_ctor_get(x_144, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_144);
x_153 = l_Lean_Expr_mvar___override(x_2);
x_154 = l_Lean_mkAppN(x_153, x_151);
lean_dec(x_151);
x_155 = lean_mk_empty_array_with_capacity(x_33);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_152);
return x_157;
}
}
else
{
uint8_t x_158; 
lean_dec(x_2);
x_158 = !lean_is_exclusive(x_144);
if (x_158 == 0)
{
return x_144;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_144, 0);
x_160 = lean_ctor_get(x_144, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_144);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
block_14:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_MVarId_assign___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__3___redArg(x_2, x_9, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_apply_3(x_8, x_11, x_5, x_12);
return x_13;
}
block_27:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = l_Array_append(lean_box(0), x_17, x_19);
lean_dec(x_19);
x_23 = l_Lean_assignDelayedMVar___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__2___redArg(x_15, x_22, x_18, x_21);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_apply_3(x_16, x_24, x_20, x_25);
return x_26;
}
block_72:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_63; 
x_43 = lean_ctor_get(x_42, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_45);
lean_inc(x_44);
x_46 = l_Lean_Name_num___override(x_44, x_45);
lean_inc(x_46);
x_47 = l_Lean_Expr_mvar___override(x_46);
x_48 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkMVarApp(x_30, x_47, x_39, x_37);
lean_inc(x_48);
x_49 = lean_alloc_closure((void*)(l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar___lam__0___boxed), 6, 3);
lean_closure_set(x_49, 0, x_48);
lean_closure_set(x_49, 1, x_36);
lean_closure_set(x_49, 2, x_35);
x_50 = lean_ctor_get(x_29, 5);
lean_inc(x_50);
x_51 = l_Lean_Expr_getAppNumArgs(x_48);
x_52 = lean_nat_add(x_50, x_51);
lean_dec(x_51);
lean_dec(x_50);
x_53 = lean_ctor_get(x_42, 0);
lean_inc(x_53);
x_54 = lean_box(0);
lean_inc(x_46);
x_55 = l_Lean_MetavarContext_addExprMVarDecl(x_53, x_46, x_54, x_38, x_40, x_41, x_37, x_52);
x_56 = lean_ctor_get(x_42, 1);
lean_inc(x_56);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_add(x_45, x_57);
lean_dec(x_45);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_44);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_ctor_get(x_42, 3);
lean_inc(x_60);
lean_dec(x_42);
x_61 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_61, 0, x_55);
lean_ctor_set(x_61, 1, x_56);
lean_ctor_set(x_61, 2, x_59);
lean_ctor_set(x_61, 3, x_60);
x_62 = lean_ctor_get_uint8(x_29, sizeof(void*)*7);
lean_dec(x_29);
x_63 = l_Lean_MetavarKind_isSyntheticOpaque(x_62);
if (x_63 == 0)
{
lean_dec(x_46);
lean_dec(x_39);
x_7 = x_61;
x_8 = x_49;
x_9 = x_48;
goto block_14;
}
else
{
if (x_34 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_48);
x_64 = l_Lean_getDelayedMVarAssignment_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__4___redArg(x_2, x_61);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_mk_empty_array_with_capacity(x_33);
x_15 = x_46;
x_16 = x_49;
x_17 = x_39;
x_18 = x_2;
x_19 = x_67;
x_20 = x_5;
x_21 = x_66;
goto block_27;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_2);
x_68 = lean_ctor_get(x_65, 0);
lean_inc(x_68);
lean_dec(x_65);
x_69 = lean_ctor_get(x_64, 1);
lean_inc(x_69);
lean_dec(x_64);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_15 = x_46;
x_16 = x_49;
x_17 = x_39;
x_18 = x_71;
x_19 = x_70;
x_20 = x_5;
x_21 = x_69;
goto block_27;
}
}
else
{
lean_dec(x_46);
lean_dec(x_39);
x_7 = x_61;
x_8 = x_49;
x_9 = x_48;
goto block_14;
}
}
}
block_107:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_79 = lean_ctor_get(x_29, 2);
lean_inc(x_79);
x_80 = lean_ctor_get(x_73, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_73, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_73, 2);
lean_inc(x_82);
x_83 = lean_unsigned_to_nat(8u);
x_84 = lean_unsigned_to_nat(2u);
x_85 = lean_nat_shiftl(x_83, x_84);
x_86 = lean_unsigned_to_nat(3u);
x_87 = lean_nat_div(x_85, x_86);
lean_dec(x_85);
x_88 = l_Nat_nextPowerOfTwo(x_87);
lean_dec(x_87);
x_89 = lean_box(0);
x_90 = lean_mk_array(x_88, x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_33);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_92, 0, x_80);
lean_ctor_set(x_92, 1, x_81);
lean_ctor_set(x_92, 2, x_82);
lean_ctor_set(x_92, 3, x_91);
lean_inc(x_5);
lean_inc(x_30);
x_93 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkAuxMVarType(x_30, x_74, x_76, x_79, x_4, x_5, x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_ctor_get(x_73, 3);
lean_inc(x_96);
lean_dec(x_73);
x_97 = lean_ctor_get(x_95, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_95, 2);
lean_inc(x_99);
lean_dec(x_95);
x_100 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
lean_ctor_set(x_100, 2, x_99);
lean_ctor_set(x_100, 3, x_96);
lean_inc(x_74);
x_35 = x_74;
x_36 = x_75;
x_37 = x_76;
x_38 = x_77;
x_39 = x_74;
x_40 = x_78;
x_41 = x_94;
x_42 = x_100;
goto block_72;
}
else
{
lean_dec(x_73);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_93, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_93, 1);
lean_inc(x_102);
lean_dec(x_93);
lean_inc(x_74);
x_35 = x_74;
x_36 = x_75;
x_37 = x_76;
x_38 = x_77;
x_39 = x_74;
x_40 = x_78;
x_41 = x_101;
x_42 = x_102;
goto block_72;
}
else
{
uint8_t x_103; 
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_2);
x_103 = !lean_is_exclusive(x_93);
if (x_103 == 0)
{
return x_93;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_93, 0);
x_105 = lean_ctor_get(x_93, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_93);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkAuxMVarType_spec__0___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_5, x_9);
if (x_10 == 1)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_19; uint8_t x_20; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_5, x_12);
lean_dec(x_5);
x_19 = lean_array_fget(x_1, x_13);
x_20 = l_Lean_Expr_isFVar(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_8, 0);
lean_inc(x_21);
x_22 = l_Lean_Expr_mvarId_x21(x_19);
lean_dec(x_19);
x_23 = l_Lean_MetavarContext_getDecl(x_21, x_22);
lean_dec(x_22);
x_24 = lean_ctor_get(x_23, 2);
lean_inc(x_24);
x_25 = l_Lean_Expr_headBeta(x_24);
lean_inc(x_7);
x_26 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkAuxMVarType_abstractRangeAux(x_1, x_13, x_25, x_7, x_8);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_36; uint8_t x_37; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_36 = lean_ctor_get(x_23, 0);
lean_inc(x_36);
lean_dec(x_23);
x_37 = l_Lean_Name_isAnonymous(x_36);
if (x_37 == 0)
{
lean_inc(x_7);
x_29 = x_36;
x_30 = x_7;
x_31 = x_28;
goto block_35;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_36);
x_38 = lean_mk_string_unchecked("x", 1, 1);
x_39 = l_Lean_Name_mkStr1(x_38);
lean_inc(x_7);
x_40 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkFreshBinderName(x_39, x_7, x_28);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_7);
x_29 = x_41;
x_30 = x_7;
x_31 = x_42;
goto block_35;
}
block_35:
{
uint8_t x_32; lean_object* x_33; 
x_32 = lean_ctor_get_uint8(x_30, sizeof(void*)*2 + 1);
lean_dec(x_30);
x_33 = l_Lean_Expr_forallE___override(x_29, x_27, x_6, x_32);
x_5 = x_13;
x_6 = x_33;
x_8 = x_31;
goto _start;
}
}
else
{
lean_dec(x_23);
lean_dec(x_6);
x_14 = x_26;
goto block_18;
}
}
else
{
lean_object* x_43; 
lean_inc(x_2);
x_43 = l_Lean_LocalContext_getFVar_x21(x_2, x_19);
lean_dec(x_19);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_43, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 3);
lean_inc(x_45);
x_46 = lean_ctor_get_uint8(x_43, sizeof(void*)*4);
lean_dec(x_43);
x_47 = l_Lean_Expr_headBeta(x_45);
lean_inc(x_7);
x_48 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkAuxMVarType_abstractRangeAux(x_1, x_13, x_47, x_7, x_8);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_Expr_forallE___override(x_44, x_49, x_6, x_46);
x_5 = x_13;
x_6 = x_51;
x_8 = x_50;
goto _start;
}
else
{
lean_dec(x_44);
lean_dec(x_6);
x_14 = x_48;
goto block_18;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_ctor_get(x_43, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_43, 3);
lean_inc(x_54);
x_55 = lean_ctor_get(x_43, 4);
lean_inc(x_55);
x_56 = lean_ctor_get_uint8(x_43, sizeof(void*)*5);
lean_dec(x_43);
if (x_4 == 0)
{
if (x_20 == 0)
{
goto block_85;
}
else
{
goto block_72;
}
}
else
{
goto block_85;
}
block_72:
{
lean_object* x_57; lean_object* x_58; 
x_57 = l_Lean_Expr_headBeta(x_54);
lean_inc(x_7);
x_58 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkAuxMVarType_abstractRangeAux(x_1, x_13, x_57, x_7, x_8);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
lean_inc(x_7);
x_61 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkAuxMVarType_abstractRangeAux(x_1, x_13, x_55, x_7, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
lean_inc(x_59);
lean_inc(x_53);
x_64 = l_Lean_Expr_letE___override(x_53, x_59, x_62, x_6, x_56);
x_65 = lean_box(x_3);
if (lean_obj_tag(x_65) == 2)
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; 
x_66 = lean_expr_lift_loose_bvars(x_64, x_9, x_12);
lean_dec(x_64);
x_67 = lean_box(0);
x_68 = lean_unbox(x_67);
x_69 = l_Lean_Expr_forallE___override(x_53, x_59, x_66, x_68);
x_5 = x_13;
x_6 = x_69;
x_8 = x_63;
goto _start;
}
else
{
lean_dec(x_65);
lean_dec(x_59);
lean_dec(x_53);
x_5 = x_13;
x_6 = x_64;
x_8 = x_63;
goto _start;
}
}
else
{
lean_dec(x_59);
lean_dec(x_53);
lean_dec(x_6);
x_14 = x_61;
goto block_18;
}
}
else
{
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_6);
x_14 = x_58;
goto block_18;
}
}
block_85:
{
uint8_t x_73; 
x_73 = lean_expr_has_loose_bvar(x_6, x_9);
if (x_73 == 0)
{
lean_object* x_74; 
lean_dec(x_55);
x_74 = lean_box(x_3);
if (lean_obj_tag(x_74) == 2)
{
lean_object* x_75; lean_object* x_76; 
x_75 = l_Lean_Expr_headBeta(x_54);
lean_inc(x_7);
x_76 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkAuxMVarType_abstractRangeAux(x_1, x_13, x_75, x_7, x_8);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_box(0);
x_80 = lean_unbox(x_79);
x_81 = l_Lean_Expr_forallE___override(x_53, x_77, x_6, x_80);
x_5 = x_13;
x_6 = x_81;
x_8 = x_78;
goto _start;
}
else
{
lean_dec(x_53);
lean_dec(x_6);
x_14 = x_76;
goto block_18;
}
}
else
{
lean_object* x_83; 
lean_dec(x_74);
lean_dec(x_54);
lean_dec(x_53);
x_83 = lean_expr_lower_loose_bvars(x_6, x_12, x_12);
lean_dec(x_6);
x_5 = x_13;
x_6 = x_83;
goto _start;
}
}
else
{
goto block_72;
}
}
}
}
block_18:
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_5 = x_13;
x_6 = x_15;
x_8 = x_16;
goto _start;
}
else
{
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_2);
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkAuxMVarType_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_foldRevM_loop___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkAuxMVarType_spec__0___redArg(x_1, x_2, x_3, x_4, x_6, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkAuxMVarType(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_get_size(x_2);
lean_inc(x_6);
x_9 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkAuxMVarType_abstractRangeAux(x_2, x_8, x_4, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Nat_foldRevM_loop___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkAuxMVarType_spec__0___redArg(x_2, x_1, x_3, x_5, x_8, x_10, x_6, x_11);
return x_12;
}
else
{
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_ExprStructEq_beq(x_4, x_1);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_ExprStructEq_beq(x_5, x_1);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_Expr_hash(x_4);
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
x_29 = l_Lean_Expr_hash(x_25);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2_spec__2_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2_spec__2_spec__2___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2___redArg(lean_object* x_1) {
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
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2_spec__2___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l_Lean_ExprStructEq_beq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__5___redArg(x_1, x_2, x_7);
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
x_13 = l_Lean_ExprStructEq_beq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__5___redArg(x_1, x_2, x_12);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__5___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Expr_hasMVar(x_2);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_4, 3);
lean_inc(x_7);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint64_t x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; lean_object* x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; size_t x_21; size_t x_22; lean_object* x_23; size_t x_24; size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_array_get_size(x_9);
x_12 = l_Lean_Expr_hash(x_2);
x_13 = lean_unsigned_to_nat(32u);
x_14 = lean_uint64_of_nat(x_13);
x_15 = lean_uint64_shift_right(x_12, x_14);
x_16 = lean_uint64_xor(x_12, x_15);
x_17 = lean_unsigned_to_nat(16u);
x_18 = lean_uint64_of_nat(x_17);
x_19 = lean_uint64_shift_right(x_16, x_18);
x_20 = lean_uint64_xor(x_16, x_19);
x_21 = lean_uint64_to_usize(x_20);
x_22 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_usize_of_nat(x_23);
x_25 = lean_usize_sub(x_22, x_24);
x_26 = lean_usize_land(x_21, x_25);
x_27 = lean_array_uget(x_9, x_26);
lean_dec(x_9);
x_28 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__0___redArg(x_2, x_27);
lean_dec(x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
lean_free_object(x_7);
lean_inc(x_2);
x_29 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elim(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_33 = x_29;
} else {
 lean_dec_ref(x_29);
 x_33 = lean_box(0);
}
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_44; size_t x_45; size_t x_46; size_t x_47; lean_object* x_48; uint8_t x_49; 
x_35 = lean_ctor_get(x_31, 0);
x_36 = lean_ctor_get(x_31, 1);
x_37 = lean_ctor_get(x_30, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_30, 2);
lean_inc(x_39);
lean_dec(x_30);
x_44 = lean_array_get_size(x_36);
x_45 = lean_usize_of_nat(x_44);
lean_dec(x_44);
x_46 = lean_usize_sub(x_45, x_24);
x_47 = lean_usize_land(x_21, x_46);
x_48 = lean_array_uget(x_36, x_47);
x_49 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__1___redArg(x_2, x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_50 = lean_nat_add(x_35, x_23);
lean_dec(x_35);
lean_inc(x_32);
x_51 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_51, 0, x_2);
lean_ctor_set(x_51, 1, x_32);
lean_ctor_set(x_51, 2, x_48);
x_52 = lean_array_uset(x_36, x_47, x_51);
x_53 = lean_unsigned_to_nat(2u);
x_54 = lean_nat_shiftl(x_50, x_53);
x_55 = lean_unsigned_to_nat(3u);
x_56 = lean_nat_div(x_54, x_55);
lean_dec(x_54);
x_57 = lean_array_get_size(x_52);
x_58 = lean_nat_dec_le(x_56, x_57);
lean_dec(x_57);
lean_dec(x_56);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2___redArg(x_52);
lean_ctor_set(x_31, 1, x_59);
lean_ctor_set(x_31, 0, x_50);
x_40 = x_31;
goto block_43;
}
else
{
lean_ctor_set(x_31, 1, x_52);
lean_ctor_set(x_31, 0, x_50);
x_40 = x_31;
goto block_43;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_box(0);
x_61 = lean_array_uset(x_36, x_47, x_60);
lean_inc(x_32);
x_62 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__5___redArg(x_2, x_32, x_48);
x_63 = lean_array_uset(x_61, x_47, x_62);
lean_ctor_set(x_31, 1, x_63);
x_40 = x_31;
goto block_43;
}
block_43:
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_38);
lean_ctor_set(x_41, 2, x_39);
lean_ctor_set(x_41, 3, x_40);
if (lean_is_scalar(x_33)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_33;
}
lean_ctor_set(x_42, 0, x_32);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_73; size_t x_74; size_t x_75; size_t x_76; lean_object* x_77; uint8_t x_78; 
x_64 = lean_ctor_get(x_31, 0);
x_65 = lean_ctor_get(x_31, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_31);
x_66 = lean_ctor_get(x_30, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_30, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_30, 2);
lean_inc(x_68);
lean_dec(x_30);
x_73 = lean_array_get_size(x_65);
x_74 = lean_usize_of_nat(x_73);
lean_dec(x_73);
x_75 = lean_usize_sub(x_74, x_24);
x_76 = lean_usize_land(x_21, x_75);
x_77 = lean_array_uget(x_65, x_76);
x_78 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__1___redArg(x_2, x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_79 = lean_nat_add(x_64, x_23);
lean_dec(x_64);
lean_inc(x_32);
x_80 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_80, 0, x_2);
lean_ctor_set(x_80, 1, x_32);
lean_ctor_set(x_80, 2, x_77);
x_81 = lean_array_uset(x_65, x_76, x_80);
x_82 = lean_unsigned_to_nat(2u);
x_83 = lean_nat_shiftl(x_79, x_82);
x_84 = lean_unsigned_to_nat(3u);
x_85 = lean_nat_div(x_83, x_84);
lean_dec(x_83);
x_86 = lean_array_get_size(x_81);
x_87 = lean_nat_dec_le(x_85, x_86);
lean_dec(x_86);
lean_dec(x_85);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2___redArg(x_81);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_79);
lean_ctor_set(x_89, 1, x_88);
x_69 = x_89;
goto block_72;
}
else
{
lean_object* x_90; 
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_79);
lean_ctor_set(x_90, 1, x_81);
x_69 = x_90;
goto block_72;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_91 = lean_box(0);
x_92 = lean_array_uset(x_65, x_76, x_91);
lean_inc(x_32);
x_93 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__5___redArg(x_2, x_32, x_77);
x_94 = lean_array_uset(x_92, x_76, x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_64);
lean_ctor_set(x_95, 1, x_94);
x_69 = x_95;
goto block_72;
}
block_72:
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_70, 0, x_66);
lean_ctor_set(x_70, 1, x_67);
lean_ctor_set(x_70, 2, x_68);
lean_ctor_set(x_70, 3, x_69);
if (lean_is_scalar(x_33)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_33;
}
lean_ctor_set(x_71, 0, x_32);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_dec(x_2);
return x_29;
}
}
else
{
lean_object* x_96; 
lean_dec(x_3);
lean_dec(x_2);
x_96 = lean_ctor_get(x_28, 0);
lean_inc(x_96);
lean_dec(x_28);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 0, x_96);
return x_7;
}
}
else
{
lean_object* x_97; lean_object* x_98; uint64_t x_99; lean_object* x_100; uint64_t x_101; uint64_t x_102; uint64_t x_103; lean_object* x_104; uint64_t x_105; uint64_t x_106; uint64_t x_107; size_t x_108; size_t x_109; lean_object* x_110; size_t x_111; size_t x_112; size_t x_113; lean_object* x_114; lean_object* x_115; 
x_97 = lean_ctor_get(x_7, 1);
lean_inc(x_97);
lean_dec(x_7);
x_98 = lean_array_get_size(x_97);
x_99 = l_Lean_Expr_hash(x_2);
x_100 = lean_unsigned_to_nat(32u);
x_101 = lean_uint64_of_nat(x_100);
x_102 = lean_uint64_shift_right(x_99, x_101);
x_103 = lean_uint64_xor(x_99, x_102);
x_104 = lean_unsigned_to_nat(16u);
x_105 = lean_uint64_of_nat(x_104);
x_106 = lean_uint64_shift_right(x_103, x_105);
x_107 = lean_uint64_xor(x_103, x_106);
x_108 = lean_uint64_to_usize(x_107);
x_109 = lean_usize_of_nat(x_98);
lean_dec(x_98);
x_110 = lean_unsigned_to_nat(1u);
x_111 = lean_usize_of_nat(x_110);
x_112 = lean_usize_sub(x_109, x_111);
x_113 = lean_usize_land(x_108, x_112);
x_114 = lean_array_uget(x_97, x_113);
lean_dec(x_97);
x_115 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__0___redArg(x_2, x_114);
lean_dec(x_114);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; 
lean_inc(x_2);
x_116 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elim(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_131; size_t x_132; size_t x_133; size_t x_134; lean_object* x_135; uint8_t x_136; 
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
x_118 = lean_ctor_get(x_117, 3);
lean_inc(x_118);
x_119 = lean_ctor_get(x_116, 0);
lean_inc(x_119);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_120 = x_116;
} else {
 lean_dec_ref(x_116);
 x_120 = lean_box(0);
}
x_121 = lean_ctor_get(x_118, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_118, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_123 = x_118;
} else {
 lean_dec_ref(x_118);
 x_123 = lean_box(0);
}
x_124 = lean_ctor_get(x_117, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_117, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_117, 2);
lean_inc(x_126);
lean_dec(x_117);
x_131 = lean_array_get_size(x_122);
x_132 = lean_usize_of_nat(x_131);
lean_dec(x_131);
x_133 = lean_usize_sub(x_132, x_111);
x_134 = lean_usize_land(x_108, x_133);
x_135 = lean_array_uget(x_122, x_134);
x_136 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__1___redArg(x_2, x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_137 = lean_nat_add(x_121, x_110);
lean_dec(x_121);
lean_inc(x_119);
x_138 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_138, 0, x_2);
lean_ctor_set(x_138, 1, x_119);
lean_ctor_set(x_138, 2, x_135);
x_139 = lean_array_uset(x_122, x_134, x_138);
x_140 = lean_unsigned_to_nat(2u);
x_141 = lean_nat_shiftl(x_137, x_140);
x_142 = lean_unsigned_to_nat(3u);
x_143 = lean_nat_div(x_141, x_142);
lean_dec(x_141);
x_144 = lean_array_get_size(x_139);
x_145 = lean_nat_dec_le(x_143, x_144);
lean_dec(x_144);
lean_dec(x_143);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; 
x_146 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2___redArg(x_139);
if (lean_is_scalar(x_123)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_123;
}
lean_ctor_set(x_147, 0, x_137);
lean_ctor_set(x_147, 1, x_146);
x_127 = x_147;
goto block_130;
}
else
{
lean_object* x_148; 
if (lean_is_scalar(x_123)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_123;
}
lean_ctor_set(x_148, 0, x_137);
lean_ctor_set(x_148, 1, x_139);
x_127 = x_148;
goto block_130;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_149 = lean_box(0);
x_150 = lean_array_uset(x_122, x_134, x_149);
lean_inc(x_119);
x_151 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__5___redArg(x_2, x_119, x_135);
x_152 = lean_array_uset(x_150, x_134, x_151);
if (lean_is_scalar(x_123)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_123;
}
lean_ctor_set(x_153, 0, x_121);
lean_ctor_set(x_153, 1, x_152);
x_127 = x_153;
goto block_130;
}
block_130:
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_128, 0, x_124);
lean_ctor_set(x_128, 1, x_125);
lean_ctor_set(x_128, 2, x_126);
lean_ctor_set(x_128, 3, x_127);
if (lean_is_scalar(x_120)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_120;
}
lean_ctor_set(x_129, 0, x_119);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
else
{
lean_dec(x_2);
return x_116;
}
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_3);
lean_dec(x_2);
x_154 = lean_ctor_get(x_115, 0);
lean_inc(x_154);
lean_dec(x_115);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_4);
return x_155;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkAuxMVarType_abstractRangeAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkAuxMVarType_abstractRangeAux(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elim_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Expr_withAppAux___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elim_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elim(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getExprMVarAssignment_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getExprMVarAssignment_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_findCore___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_findCore___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_mapMUnsafe_map___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp_spec__2(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimApp(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MVarId_isAssignable___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MVarId_isAssignable___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_assignDelayedMVar___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_assignDelayedMVar___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MVarId_assign___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getDelayedMVarAssignment_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__4___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getDelayedMVarAssignment_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__4(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__5_spec__5(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = l_Array_foldlMUnsafe_fold___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar_spec__5(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar(x_1, x_2, x_3, x_7, x_5, x_6);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkAuxMVarType_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Nat_foldRevM_loop___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkAuxMVarType_spec__0___redArg(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkAuxMVarType_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Nat_foldRevM_loop___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkAuxMVarType_spec__0(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkAuxMVarType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkAuxMVarType(x_1, x_2, x_8, x_4, x_9, x_6, x_7);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_elimMVarDeps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Expr_hasMVar(x_2);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 2);
lean_inc(x_9);
x_10 = lean_unsigned_to_nat(8u);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_nat_shiftl(x_10, x_12);
x_14 = lean_unsigned_to_nat(3u);
x_15 = lean_nat_div(x_13, x_14);
lean_dec(x_13);
x_16 = l_Nat_nextPowerOfTwo(x_15);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = lean_mk_array(x_16, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_8);
lean_ctor_set(x_20, 2, x_9);
lean_ctor_set(x_20, 3, x_19);
x_21 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elim(x_1, x_2, x_3, x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_21, 1);
x_24 = lean_ctor_get(x_4, 3);
lean_inc(x_24);
lean_dec(x_4);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_23, 2);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set(x_28, 3, x_24);
lean_ctor_set(x_21, 1, x_28);
return x_21;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_21, 0);
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_21);
x_31 = lean_ctor_get(x_4, 3);
lean_inc(x_31);
lean_dec(x_4);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_30, 2);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set(x_35, 3, x_31);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
lean_dec(x_4);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_elimMVarDeps___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MetavarContext_MkBinding_elimMVarDeps(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_revert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_mk_empty_array_with_capacity(x_5);
x_7 = lean_box(0);
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_ctor_get(x_4, 2);
x_11 = lean_unsigned_to_nat(8u);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_nat_shiftl(x_11, x_12);
x_14 = lean_unsigned_to_nat(3u);
x_15 = lean_nat_div(x_13, x_14);
lean_dec(x_13);
x_16 = l_Nat_nextPowerOfTwo(x_15);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = lean_mk_array(x_16, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_18);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_9);
lean_ctor_set(x_20, 2, x_10);
lean_ctor_set(x_20, 3, x_19);
x_21 = lean_unbox(x_7);
x_22 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_elimMVar(x_1, x_2, x_6, x_21, x_3, x_20);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_22, 1);
x_25 = lean_ctor_get(x_4, 3);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_24, 2);
lean_inc(x_28);
lean_dec(x_24);
lean_inc(x_25);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_22, 1, x_29);
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_22, 0);
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_22);
x_32 = lean_ctor_get(x_4, 3);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_31, 2);
lean_inc(x_35);
lean_dec(x_31);
lean_inc(x_32);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_36, 2, x_35);
lean_ctor_set(x_36, 3, x_32);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_30);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_revert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MetavarContext_MkBinding_revert(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_abstractRange(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_MetavarContext_MkBinding_elimMVarDeps(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_expr_abstract_range(x_8, x_2, x_1);
lean_dec(x_8);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
x_12 = lean_expr_abstract_range(x_10, x_2, x_1);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_abstractRange___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_MetavarContext_MkBinding_abstractRange(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkLambda_x27(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_Lean_Expr_lam___override(x_1, x_3, x_4, x_2);
return x_6;
}
else
{
if (lean_obj_tag(x_4) == 5)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
x_12 = l_Lean_Expr_lam___override(x_1, x_3, x_4, x_2);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_expr_has_loose_bvar(x_8, x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_expr_lower_loose_bvars(x_8, x_14, x_14);
lean_dec(x_8);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_8);
x_16 = l_Lean_Expr_lam___override(x_1, x_3, x_4, x_2);
return x_16;
}
}
}
else
{
lean_object* x_17; 
lean_dec(x_7);
x_17 = l_Lean_Expr_lam___override(x_1, x_3, x_4, x_2);
return x_17;
}
}
else
{
lean_object* x_18; 
x_18 = l_Lean_Expr_lam___override(x_1, x_3, x_4, x_2);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkLambda_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = lean_unbox(x_5);
lean_dec(x_5);
x_8 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkLambda_x27(x_1, x_6, x_3, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at___Lean_MetavarContext_MkBinding_mkBinding_spec__0___redArg(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_7, x_11);
if (x_12 == 1)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_27; lean_object* x_32; uint8_t x_33; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_7, x_14);
lean_dec(x_7);
x_32 = lean_array_fget(x_1, x_15);
x_33 = l_Lean_Expr_isFVar(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_34 = lean_ctor_get(x_10, 0);
lean_inc(x_34);
x_35 = l_Lean_Expr_mvarId_x21(x_32);
lean_dec(x_32);
x_36 = l_Lean_MetavarContext_getDecl(x_34, x_35);
lean_dec(x_35);
x_47 = lean_ctor_get(x_36, 2);
lean_inc(x_47);
x_48 = l_Lean_Expr_headBeta(x_47);
lean_inc(x_9);
x_49 = l_Lean_MetavarContext_MkBinding_elimMVarDeps(x_1, x_48, x_9, x_10);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_expr_abstract_range(x_50, x_15, x_1);
lean_dec(x_50);
x_37 = x_52;
x_38 = x_51;
goto block_46;
}
else
{
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_49, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
lean_dec(x_49);
x_37 = x_53;
x_38 = x_54;
goto block_46;
}
else
{
lean_dec(x_36);
lean_dec(x_8);
x_27 = x_49;
goto block_31;
}
}
block_46:
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_36, 0);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l_Lean_Name_isAnonymous(x_39);
if (x_40 == 0)
{
lean_inc(x_9);
x_16 = x_37;
x_17 = x_39;
x_18 = x_9;
x_19 = x_38;
goto block_26;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_39);
x_41 = lean_mk_string_unchecked("x", 1, 1);
x_42 = l_Lean_Name_mkStr1(x_41);
lean_inc(x_9);
x_43 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkFreshBinderName(x_42, x_9, x_38);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_9);
x_16 = x_37;
x_17 = x_44;
x_18 = x_9;
x_19 = x_45;
goto block_26;
}
}
}
else
{
lean_object* x_55; 
lean_inc(x_4);
x_55 = l_Lean_LocalContext_getFVar_x21(x_4, x_32);
lean_dec(x_32);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_55, 2);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 3);
lean_inc(x_57);
x_58 = lean_ctor_get_uint8(x_55, sizeof(void*)*4);
lean_dec(x_55);
if (x_5 == 0)
{
if (x_33 == 0)
{
goto block_77;
}
else
{
goto block_73;
}
}
else
{
goto block_77;
}
block_65:
{
if (x_2 == 0)
{
lean_object* x_61; 
x_61 = l_Lean_Expr_forallE___override(x_56, x_59, x_8, x_58);
x_7 = x_15;
x_8 = x_61;
x_10 = x_60;
goto _start;
}
else
{
lean_object* x_63; 
x_63 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkLambda_x27(x_56, x_58, x_59, x_8, x_3);
x_7 = x_15;
x_8 = x_63;
x_10 = x_60;
goto _start;
}
}
block_73:
{
lean_object* x_66; lean_object* x_67; 
x_66 = l_Lean_Expr_headBeta(x_57);
lean_inc(x_9);
x_67 = l_Lean_MetavarContext_MkBinding_elimMVarDeps(x_1, x_66, x_9, x_10);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_expr_abstract_range(x_68, x_15, x_1);
lean_dec(x_68);
x_59 = x_70;
x_60 = x_69;
goto block_65;
}
else
{
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_67, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
lean_dec(x_67);
x_59 = x_71;
x_60 = x_72;
goto block_65;
}
else
{
lean_dec(x_56);
lean_dec(x_8);
x_27 = x_67;
goto block_31;
}
}
}
block_77:
{
uint8_t x_74; 
x_74 = lean_expr_has_loose_bvar(x_8, x_11);
if (x_74 == 0)
{
lean_object* x_75; 
lean_dec(x_57);
lean_dec(x_56);
x_75 = lean_expr_lower_loose_bvars(x_8, x_14, x_14);
lean_dec(x_8);
x_7 = x_15;
x_8 = x_75;
goto _start;
}
else
{
goto block_73;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_88; lean_object* x_89; 
x_78 = lean_ctor_get(x_55, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_55, 3);
lean_inc(x_79);
x_80 = lean_ctor_get(x_55, 4);
lean_inc(x_80);
x_81 = lean_ctor_get_uint8(x_55, sizeof(void*)*5);
lean_dec(x_55);
if (x_6 == 0)
{
if (x_33 == 0)
{
goto block_107;
}
else
{
goto block_103;
}
}
else
{
goto block_107;
}
block_87:
{
lean_object* x_85; 
x_85 = l_Lean_Expr_letE___override(x_78, x_82, x_83, x_8, x_81);
x_7 = x_15;
x_8 = x_85;
x_10 = x_84;
goto _start;
}
block_96:
{
lean_object* x_90; 
lean_inc(x_9);
x_90 = l_Lean_MetavarContext_MkBinding_elimMVarDeps(x_1, x_80, x_9, x_89);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_expr_abstract_range(x_91, x_15, x_1);
lean_dec(x_91);
x_82 = x_88;
x_83 = x_93;
x_84 = x_92;
goto block_87;
}
else
{
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_90, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_90, 1);
lean_inc(x_95);
lean_dec(x_90);
x_82 = x_88;
x_83 = x_94;
x_84 = x_95;
goto block_87;
}
else
{
lean_dec(x_88);
lean_dec(x_78);
lean_dec(x_8);
x_27 = x_90;
goto block_31;
}
}
}
block_103:
{
lean_object* x_97; 
lean_inc(x_9);
x_97 = l_Lean_MetavarContext_MkBinding_elimMVarDeps(x_1, x_79, x_9, x_10);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_expr_abstract_range(x_98, x_15, x_1);
lean_dec(x_98);
x_88 = x_100;
x_89 = x_99;
goto block_96;
}
else
{
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_97, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_97, 1);
lean_inc(x_102);
lean_dec(x_97);
x_88 = x_101;
x_89 = x_102;
goto block_96;
}
else
{
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_8);
x_27 = x_97;
goto block_31;
}
}
}
block_107:
{
uint8_t x_104; 
x_104 = lean_expr_has_loose_bvar(x_8, x_11);
if (x_104 == 0)
{
lean_object* x_105; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
x_105 = lean_expr_lower_loose_bvars(x_8, x_14, x_14);
lean_dec(x_8);
x_7 = x_15;
x_8 = x_105;
goto _start;
}
else
{
goto block_103;
}
}
}
}
block_26:
{
if (x_2 == 0)
{
uint8_t x_20; lean_object* x_21; 
x_20 = lean_ctor_get_uint8(x_18, sizeof(void*)*2 + 1);
lean_dec(x_18);
x_21 = l_Lean_Expr_forallE___override(x_17, x_16, x_8, x_20);
x_7 = x_15;
x_8 = x_21;
x_10 = x_19;
goto _start;
}
else
{
uint8_t x_23; lean_object* x_24; 
x_23 = lean_ctor_get_uint8(x_18, sizeof(void*)*2 + 1);
lean_dec(x_18);
x_24 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_mkLambda_x27(x_17, x_23, x_16, x_8, x_3);
x_7 = x_15;
x_8 = x_24;
x_10 = x_19;
goto _start;
}
}
block_31:
{
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_7 = x_15;
x_8 = x_28;
x_10 = x_29;
goto _start;
}
else
{
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_4);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at___Lean_MetavarContext_MkBinding_mkBinding_spec__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Nat_foldRevM_loop___at___Lean_MetavarContext_MkBinding_mkBinding_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_mkBinding(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_get_size(x_3);
lean_inc(x_8);
x_11 = l_Lean_MetavarContext_MkBinding_elimMVarDeps(x_3, x_4, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_expr_abstract_range(x_12, x_10, x_3);
lean_dec(x_12);
x_15 = l_Nat_foldRevM_loop___at___Lean_MetavarContext_MkBinding_mkBinding_spec__0___redArg(x_3, x_1, x_7, x_2, x_5, x_6, x_10, x_14, x_8, x_13);
return x_15;
}
else
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = l_Nat_foldRevM_loop___at___Lean_MetavarContext_MkBinding_mkBinding_spec__0___redArg(x_3, x_1, x_7, x_2, x_5, x_6, x_10, x_16, x_8, x_17);
return x_18;
}
else
{
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at___Lean_MetavarContext_MkBinding_mkBinding_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = lean_unbox(x_6);
lean_dec(x_6);
x_15 = l_Nat_foldRevM_loop___at___Lean_MetavarContext_MkBinding_mkBinding_spec__0___redArg(x_1, x_11, x_12, x_4, x_13, x_14, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at___Lean_MetavarContext_MkBinding_mkBinding_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = lean_unbox(x_6);
lean_dec(x_6);
x_17 = l_Nat_foldRevM_loop___at___Lean_MetavarContext_MkBinding_mkBinding_spec__0(x_1, x_13, x_14, x_4, x_15, x_16, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_MkBinding_mkBinding___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = lean_unbox(x_6);
lean_dec(x_6);
x_13 = lean_unbox(x_7);
lean_dec(x_7);
x_14 = l_Lean_MetavarContext_MkBinding_mkBinding(x_10, x_2, x_3, x_4, x_11, x_12, x_13, x_8, x_9);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_elimMVarDeps(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_box(1);
x_8 = lean_box(0);
lean_inc(x_6);
x_9 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*2, x_3);
x_10 = lean_unbox(x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*2 + 1, x_10);
x_11 = l_Lean_MetavarContext_MkBinding_elimMVarDeps(x_1, x_2, x_9, x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_elimMVarDeps___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_MetavarContext_elimMVarDeps(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_revert(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_box(1);
x_8 = lean_box(0);
lean_inc(x_6);
x_9 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*2, x_3);
x_10 = lean_unbox(x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*2 + 1, x_10);
x_11 = l_Lean_MetavarContext_MkBinding_revert(x_1, x_2, x_9, x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_revert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_MetavarContext_revert(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_MetavarContext_mkBinding_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_uget(x_1, x_2);
x_13 = l_Lean_Expr_isMVar(x_12);
if (x_13 == 0)
{
lean_dec(x_12);
x_5 = x_4;
goto block_10;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Expr_mvarId_x21(x_12);
lean_dec(x_12);
x_15 = l_Lean_MVarIdSet_insert(x_4, x_14);
x_5 = x_15;
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
LEAN_EXPORT lean_object* l_Lean_MetavarContext_mkBinding(uint8_t x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_box(0);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_get_size(x_2);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_dec(x_20);
x_10 = x_18;
goto block_17;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_le(x_20, x_20);
if (x_22 == 0)
{
lean_dec(x_20);
x_10 = x_18;
goto block_17;
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; 
x_23 = lean_usize_of_nat(x_19);
x_24 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_25 = l_Array_foldlMUnsafe_fold___at___Lean_MetavarContext_mkBinding_spec__0(x_2, x_23, x_24, x_18);
x_10 = x_25;
goto block_17;
}
}
block_17:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_10);
x_15 = lean_unbox(x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*2, x_15);
lean_ctor_set_uint8(x_14, sizeof(void*)*2 + 1, x_7);
x_16 = l_Lean_MetavarContext_MkBinding_mkBinding(x_1, x_11, x_2, x_3, x_4, x_5, x_6, x_14, x_9);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_MetavarContext_mkBinding_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_MetavarContext_mkBinding_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_mkBinding___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = lean_unbox(x_7);
lean_dec(x_7);
x_15 = l_Lean_MetavarContext_mkBinding(x_10, x_2, x_3, x_11, x_12, x_13, x_14, x_8, x_9);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_mkLambda(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_box(1);
x_10 = lean_unbox(x_9);
x_11 = l_Lean_MetavarContext_mkBinding(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_mkLambda___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = lean_unbox(x_6);
lean_dec(x_6);
x_13 = l_Lean_MetavarContext_mkLambda(x_1, x_2, x_9, x_10, x_11, x_12, x_7, x_8);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_mkForall(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
x_10 = lean_unbox(x_8);
x_11 = l_Lean_MetavarContext_mkBinding(x_9, x_1, x_2, x_3, x_4, x_10, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_mkForall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = l_Lean_MetavarContext_mkForall(x_1, x_2, x_8, x_9, x_10, x_6, x_7);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_abstractRange(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_box(0);
x_8 = lean_box(1);
x_9 = lean_box(0);
lean_inc(x_6);
x_10 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_unbox(x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*2, x_11);
x_12 = lean_unbox(x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*2 + 1, x_12);
x_13 = l_Lean_MetavarContext_MkBinding_elimMVarDeps(x_3, x_1, x_10, x_5);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_expr_abstract_range(x_15, x_2, x_3);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_expr_abstract_range(x_17, x_2, x_3);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_abstractRange___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_MetavarContext_abstractRange(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_collectForwardDeps(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_box(1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*2, x_2);
x_10 = lean_unbox(x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*2 + 1, x_10);
x_11 = l_Lean_MetavarContext_MkBinding_collectForwardDeps(x_5, x_1, x_9, x_4);
lean_dec(x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_collectForwardDeps___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_MetavarContext_collectForwardDeps(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_isWellFormed___redArg___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_box(x_2);
x_8 = lean_apply_2(x_1, lean_box(0), x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = l_Lean_MetavarContext_isWellFormed___redArg(x_3, x_4, x_5, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_isWellFormed___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = l_Lean_MetavarContext_getDecl(x_7, x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_mk_empty_array_with_capacity(x_10);
lean_inc(x_2);
x_12 = l_Lean_LocalContext_isSubPrefixOf(x_9, x_2, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_box(x_12);
lean_inc(x_5);
lean_inc(x_4);
x_14 = lean_alloc_closure((void*)(l_Lean_MetavarContext_isWellFormed___redArg___lam__0___boxed), 6, 5);
lean_closure_set(x_14, 0, x_3);
lean_closure_set(x_14, 1, x_13);
lean_closure_set(x_14, 2, x_4);
lean_closure_set(x_14, 3, x_5);
lean_closure_set(x_14, 4, x_2);
x_15 = l_Lean_getExprMVarAssignment_x3f___redArg(x_4, x_5, x_1);
x_16 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_15, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_box(x_12);
x_18 = lean_apply_2(x_3, lean_box(0), x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_isWellFormed___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_box(x_6);
x_8 = lean_apply_2(x_1, lean_box(0), x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = l_Lean_MetavarContext_isWellFormed___redArg(x_2, x_3, x_4, x_5);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_isWellFormed___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8) {
_start:
{
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
x_9 = l_Lean_MetavarContext_isWellFormed___redArg(x_1, x_2, x_3, x_4);
x_10 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_9, x_6);
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
x_11 = lean_box(x_8);
x_12 = lean_apply_2(x_7, lean_box(0), x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_isWellFormed___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_box(x_6);
x_8 = lean_apply_2(x_1, lean_box(0), x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = l_Lean_MetavarContext_isWellFormed___redArg(x_2, x_3, x_4, x_5);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_isWellFormed___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8) {
_start:
{
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
x_9 = l_Lean_MetavarContext_isWellFormed___redArg(x_1, x_2, x_3, x_4);
x_10 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_9, x_6);
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
x_11 = lean_box(x_8);
x_12 = lean_apply_2(x_7, lean_box(0), x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_isWellFormed___redArg___lam__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8) {
_start:
{
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(x_8);
x_10 = lean_apply_2(x_1, lean_box(0), x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = l_Lean_MetavarContext_isWellFormed___redArg(x_2, x_3, x_4, x_5);
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_11, x_7);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_isWellFormed___redArg___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8) {
_start:
{
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
x_9 = l_Lean_MetavarContext_isWellFormed___redArg(x_1, x_2, x_3, x_4);
x_10 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_9, x_6);
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
x_11 = lean_box(x_8);
x_12 = lean_apply_2(x_7, lean_box(0), x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_isWellFormed___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 1:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = l_Lean_LocalContext_contains(x_3, x_7);
lean_dec(x_7);
x_9 = lean_box(x_8);
x_10 = lean_apply_2(x_6, lean_box(0), x_9);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_2);
x_15 = lean_alloc_closure((void*)(l_Lean_MetavarContext_isWellFormed___redArg___lam__1), 7, 6);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_3);
lean_closure_set(x_15, 2, x_13);
lean_closure_set(x_15, 3, x_1);
lean_closure_set(x_15, 4, x_2);
lean_closure_set(x_15, 5, x_11);
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_16, x_15);
return x_17;
}
case 5:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_30; 
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_20);
x_23 = lean_alloc_closure((void*)(l_Lean_MetavarContext_isWellFormed___redArg___lam__2___boxed), 6, 5);
lean_closure_set(x_23, 0, x_20);
lean_closure_set(x_23, 1, x_1);
lean_closure_set(x_23, 2, x_2);
lean_closure_set(x_23, 3, x_3);
lean_closure_set(x_23, 4, x_22);
lean_inc(x_20);
lean_inc(x_18);
x_24 = lean_alloc_closure((void*)(l_Lean_MetavarContext_isWellFormed___redArg___lam__3___boxed), 8, 7);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_2);
lean_closure_set(x_24, 2, x_3);
lean_closure_set(x_24, 3, x_21);
lean_closure_set(x_24, 4, x_18);
lean_closure_set(x_24, 5, x_23);
lean_closure_set(x_24, 6, x_20);
x_30 = l_Lean_Expr_hasExprMVar(x_4);
if (x_30 == 0)
{
uint8_t x_31; 
x_31 = l_Lean_Expr_hasFVar(x_4);
lean_dec(x_4);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_box(1);
x_33 = lean_unbox(x_32);
x_25 = x_33;
goto block_29;
}
else
{
x_25 = x_30;
goto block_29;
}
}
else
{
lean_object* x_34; uint8_t x_35; 
lean_dec(x_4);
x_34 = lean_box(0);
x_35 = lean_unbox(x_34);
x_25 = x_35;
goto block_29;
}
block_29:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_box(x_25);
x_27 = lean_apply_2(x_20, lean_box(0), x_26);
x_28 = lean_apply_4(x_18, lean_box(0), lean_box(0), x_27, x_24);
return x_28;
}
}
case 6:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_4, 2);
lean_inc(x_40);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_38);
x_41 = lean_alloc_closure((void*)(l_Lean_MetavarContext_isWellFormed___redArg___lam__4___boxed), 6, 5);
lean_closure_set(x_41, 0, x_38);
lean_closure_set(x_41, 1, x_1);
lean_closure_set(x_41, 2, x_2);
lean_closure_set(x_41, 3, x_3);
lean_closure_set(x_41, 4, x_40);
lean_inc(x_38);
lean_inc(x_36);
x_42 = lean_alloc_closure((void*)(l_Lean_MetavarContext_isWellFormed___redArg___lam__5___boxed), 8, 7);
lean_closure_set(x_42, 0, x_1);
lean_closure_set(x_42, 1, x_2);
lean_closure_set(x_42, 2, x_3);
lean_closure_set(x_42, 3, x_39);
lean_closure_set(x_42, 4, x_36);
lean_closure_set(x_42, 5, x_41);
lean_closure_set(x_42, 6, x_38);
x_48 = l_Lean_Expr_hasExprMVar(x_4);
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = l_Lean_Expr_hasFVar(x_4);
lean_dec(x_4);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_box(1);
x_51 = lean_unbox(x_50);
x_43 = x_51;
goto block_47;
}
else
{
x_43 = x_48;
goto block_47;
}
}
else
{
lean_object* x_52; uint8_t x_53; 
lean_dec(x_4);
x_52 = lean_box(0);
x_53 = lean_unbox(x_52);
x_43 = x_53;
goto block_47;
}
block_47:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_box(x_43);
x_45 = lean_apply_2(x_38, lean_box(0), x_44);
x_46 = lean_apply_4(x_36, lean_box(0), lean_box(0), x_45, x_42);
return x_46;
}
}
case 7:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_66; 
x_54 = lean_ctor_get(x_1, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_1, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_ctor_get(x_4, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_4, 2);
lean_inc(x_58);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_56);
x_59 = lean_alloc_closure((void*)(l_Lean_MetavarContext_isWellFormed___redArg___lam__4___boxed), 6, 5);
lean_closure_set(x_59, 0, x_56);
lean_closure_set(x_59, 1, x_1);
lean_closure_set(x_59, 2, x_2);
lean_closure_set(x_59, 3, x_3);
lean_closure_set(x_59, 4, x_58);
lean_inc(x_56);
lean_inc(x_54);
x_60 = lean_alloc_closure((void*)(l_Lean_MetavarContext_isWellFormed___redArg___lam__5___boxed), 8, 7);
lean_closure_set(x_60, 0, x_1);
lean_closure_set(x_60, 1, x_2);
lean_closure_set(x_60, 2, x_3);
lean_closure_set(x_60, 3, x_57);
lean_closure_set(x_60, 4, x_54);
lean_closure_set(x_60, 5, x_59);
lean_closure_set(x_60, 6, x_56);
x_66 = l_Lean_Expr_hasExprMVar(x_4);
if (x_66 == 0)
{
uint8_t x_67; 
x_67 = l_Lean_Expr_hasFVar(x_4);
lean_dec(x_4);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_box(1);
x_69 = lean_unbox(x_68);
x_61 = x_69;
goto block_65;
}
else
{
x_61 = x_66;
goto block_65;
}
}
else
{
lean_object* x_70; uint8_t x_71; 
lean_dec(x_4);
x_70 = lean_box(0);
x_71 = lean_unbox(x_70);
x_61 = x_71;
goto block_65;
}
block_65:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_box(x_61);
x_63 = lean_apply_2(x_56, lean_box(0), x_62);
x_64 = lean_apply_4(x_54, lean_box(0), lean_box(0), x_63, x_60);
return x_64;
}
}
case 8:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_86; 
x_72 = lean_ctor_get(x_1, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_1, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_ctor_get(x_4, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_4, 2);
lean_inc(x_76);
x_77 = lean_ctor_get(x_4, 3);
lean_inc(x_77);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_74);
x_78 = lean_alloc_closure((void*)(l_Lean_MetavarContext_isWellFormed___redArg___lam__4___boxed), 6, 5);
lean_closure_set(x_78, 0, x_74);
lean_closure_set(x_78, 1, x_1);
lean_closure_set(x_78, 2, x_2);
lean_closure_set(x_78, 3, x_3);
lean_closure_set(x_78, 4, x_77);
lean_inc(x_72);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_74);
x_79 = lean_alloc_closure((void*)(l_Lean_MetavarContext_isWellFormed___redArg___lam__9___boxed), 8, 7);
lean_closure_set(x_79, 0, x_74);
lean_closure_set(x_79, 1, x_1);
lean_closure_set(x_79, 2, x_2);
lean_closure_set(x_79, 3, x_3);
lean_closure_set(x_79, 4, x_76);
lean_closure_set(x_79, 5, x_72);
lean_closure_set(x_79, 6, x_78);
lean_inc(x_74);
lean_inc(x_72);
x_80 = lean_alloc_closure((void*)(l_Lean_MetavarContext_isWellFormed___redArg___lam__6___boxed), 8, 7);
lean_closure_set(x_80, 0, x_1);
lean_closure_set(x_80, 1, x_2);
lean_closure_set(x_80, 2, x_3);
lean_closure_set(x_80, 3, x_75);
lean_closure_set(x_80, 4, x_72);
lean_closure_set(x_80, 5, x_79);
lean_closure_set(x_80, 6, x_74);
x_86 = l_Lean_Expr_hasExprMVar(x_4);
if (x_86 == 0)
{
uint8_t x_87; 
x_87 = l_Lean_Expr_hasFVar(x_4);
lean_dec(x_4);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_box(1);
x_89 = lean_unbox(x_88);
x_81 = x_89;
goto block_85;
}
else
{
x_81 = x_86;
goto block_85;
}
}
else
{
lean_object* x_90; uint8_t x_91; 
lean_dec(x_4);
x_90 = lean_box(0);
x_91 = lean_unbox(x_90);
x_81 = x_91;
goto block_85;
}
block_85:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_box(x_81);
x_83 = lean_apply_2(x_74, lean_box(0), x_82);
x_84 = lean_apply_4(x_72, lean_box(0), lean_box(0), x_83, x_80);
return x_84;
}
}
case 10:
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_4, 1);
lean_inc(x_92);
lean_dec(x_4);
x_4 = x_92;
goto _start;
}
case 11:
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_4, 2);
lean_inc(x_94);
lean_dec(x_4);
x_4 = x_94;
goto _start;
}
default: 
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_96 = lean_ctor_get(x_1, 0);
lean_inc(x_96);
lean_dec(x_1);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_98 = lean_box(1);
x_99 = lean_apply_2(x_97, lean_box(0), x_98);
return x_99;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_isWellFormed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_MetavarContext_isWellFormed___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_isWellFormed___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l_Lean_MetavarContext_isWellFormed___redArg___lam__0(x_1, x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_isWellFormed___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_6);
lean_dec(x_6);
x_8 = l_Lean_MetavarContext_isWellFormed___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_isWellFormed___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_8);
lean_dec(x_8);
x_10 = l_Lean_MetavarContext_isWellFormed___redArg___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_isWellFormed___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_6);
lean_dec(x_6);
x_8 = l_Lean_MetavarContext_isWellFormed___redArg___lam__4(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_isWellFormed___redArg___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_8);
lean_dec(x_8);
x_10 = l_Lean_MetavarContext_isWellFormed___redArg___lam__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_isWellFormed___redArg___lam__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_8);
lean_dec(x_8);
x_10 = l_Lean_MetavarContext_isWellFormed___redArg___lam__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_isWellFormed___redArg___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_8);
lean_dec(x_8);
x_10 = l_Lean_MetavarContext_isWellFormed___redArg___lam__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_LevelMVarToParam_instMonadMCtxM___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_LevelMVarToParam_instMonadMCtxM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_LevelMVarToParam_instMonadMCtxM___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_box(0);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_apply_1(x_1, x_5);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 3);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_8);
lean_ctor_set(x_10, 3, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_LevelMVarToParam_instMonadMCtxM___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_apply_1(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
lean_ctor_set(x_6, 0, x_3);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_LevelMVarToParam_instMonadMCtxM___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_apply_1(x_3, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_4, x_9, x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_apply_1(x_7, x_12);
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
x_16 = lean_apply_1(x_7, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_LevelMVarToParam_instMonadMCtxM___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_apply_1(x_3, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_4, x_9, x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_7);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_LevelMVarToParam_instMonadMCtxM___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_apply_1(x_3, x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_apply_2(x_4, x_8, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_MetavarContext_LevelMVarToParam_instMonadMCtxM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_1 = lean_alloc_closure((void*)(l_Lean_MetavarContext_LevelMVarToParam_instMonadMCtxM___lam__0___boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_MetavarContext_LevelMVarToParam_instMonadMCtxM___lam__1___boxed), 3, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_MetavarContext_LevelMVarToParam_instMonadMCtxM___lam__2___boxed), 3, 0);
x_4 = lean_alloc_closure((void*)(l_Lean_MetavarContext_LevelMVarToParam_instMonadMCtxM___lam__3), 5, 0);
x_5 = lean_alloc_closure((void*)(l_Lean_MetavarContext_LevelMVarToParam_instMonadMCtxM___lam__4), 5, 0);
x_6 = lean_alloc_closure((void*)(l_Lean_MetavarContext_LevelMVarToParam_instMonadMCtxM___lam__5), 5, 0);
x_7 = lean_alloc_closure((void*)(l_Lean_MetavarContext_LevelMVarToParam_instMonadMCtxM___lam__6), 5, 0);
x_8 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_9 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_10 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_11 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_12 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_13 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_14 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_9);
x_16 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 2, x_11);
lean_ctor_set(x_16, 3, x_12);
lean_ctor_set(x_16, 4, x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
lean_inc(x_17);
x_18 = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(x_18, 0, lean_box(0));
lean_closure_set(x_18, 1, lean_box(0));
lean_closure_set(x_18, 2, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_4);
lean_inc(x_17);
x_20 = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(x_20, 0, lean_box(0));
lean_closure_set(x_20, 1, lean_box(0));
lean_closure_set(x_20, 2, x_17);
x_21 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_5);
lean_ctor_set(x_21, 3, x_6);
lean_ctor_set(x_21, 4, x_7);
x_22 = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(x_22, 0, lean_box(0));
lean_closure_set(x_22, 1, lean_box(0));
lean_closure_set(x_22, 2, x_17);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_24, 0, lean_box(0));
lean_closure_set(x_24, 1, lean_box(0));
lean_closure_set(x_24, 2, x_23);
lean_closure_set(x_24, 3, lean_box(0));
lean_closure_set(x_24, 4, lean_box(0));
lean_closure_set(x_24, 5, x_1);
lean_closure_set(x_24, 6, x_2);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_3);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_LevelMVarToParam_instMonadMCtxM___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MetavarContext_LevelMVarToParam_instMonadMCtxM___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_LevelMVarToParam_instMonadMCtxM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MetavarContext_LevelMVarToParam_instMonadMCtxM___lam__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_LevelMVarToParam_instMonadMCtxM___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MetavarContext_LevelMVarToParam_instMonadMCtxM___lam__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_LevelMVarToParam_instMonadCacheExprStructEqExprM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; lean_object* x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; size_t x_19; size_t x_20; lean_object* x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_array_get_size(x_7);
x_10 = l_Lean_Expr_hash(x_2);
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
x_25 = lean_array_uget(x_7, x_24);
lean_dec(x_7);
x_26 = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(x_1, x_2, x_25);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 0, x_26);
return x_5;
}
else
{
lean_object* x_27; lean_object* x_28; uint64_t x_29; lean_object* x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; lean_object* x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; size_t x_38; size_t x_39; lean_object* x_40; size_t x_41; size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_27 = lean_ctor_get(x_5, 1);
lean_inc(x_27);
lean_dec(x_5);
x_28 = lean_array_get_size(x_27);
x_29 = l_Lean_Expr_hash(x_2);
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
x_44 = lean_array_uget(x_27, x_43);
lean_dec(x_27);
x_45 = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(x_1, x_2, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_4);
return x_46;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_LevelMVarToParam_instMonadCacheExprStructEqExprM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_19; uint64_t x_20; lean_object* x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; size_t x_29; size_t x_30; lean_object* x_31; size_t x_32; size_t x_33; size_t x_34; lean_object* x_35; uint8_t x_36; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_box(0);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 2);
lean_inc(x_14);
lean_dec(x_6);
x_19 = lean_array_get_size(x_10);
x_20 = l_Lean_Expr_hash(x_3);
x_21 = lean_unsigned_to_nat(32u);
x_22 = lean_uint64_of_nat(x_21);
x_23 = lean_uint64_shift_right(x_20, x_22);
x_24 = lean_uint64_xor(x_20, x_23);
x_25 = lean_unsigned_to_nat(16u);
x_26 = lean_uint64_of_nat(x_25);
x_27 = lean_uint64_shift_right(x_24, x_26);
x_28 = lean_uint64_xor(x_24, x_27);
x_29 = lean_uint64_to_usize(x_28);
x_30 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_usize_of_nat(x_31);
x_33 = lean_usize_sub(x_30, x_32);
x_34 = lean_usize_land(x_29, x_33);
x_35 = lean_array_uget(x_10, x_34);
lean_inc(x_35);
lean_inc(x_3);
lean_inc(x_1);
x_36 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_1, x_3, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_1);
x_37 = lean_nat_add(x_9, x_31);
lean_dec(x_9);
x_38 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_38, 0, x_3);
lean_ctor_set(x_38, 1, x_4);
lean_ctor_set(x_38, 2, x_35);
x_39 = lean_array_uset(x_10, x_34, x_38);
x_40 = lean_unsigned_to_nat(2u);
x_41 = lean_nat_shiftl(x_37, x_40);
x_42 = lean_unsigned_to_nat(3u);
x_43 = lean_nat_div(x_41, x_42);
lean_dec(x_41);
x_44 = lean_array_get_size(x_39);
x_45 = lean_nat_dec_le(x_43, x_44);
lean_dec(x_44);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_2, x_39);
lean_ctor_set(x_7, 1, x_46);
lean_ctor_set(x_7, 0, x_37);
x_15 = x_7;
goto block_18;
}
else
{
lean_dec(x_2);
lean_ctor_set(x_7, 1, x_39);
lean_ctor_set(x_7, 0, x_37);
x_15 = x_7;
goto block_18;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_2);
x_47 = lean_box(0);
x_48 = lean_array_uset(x_10, x_34, x_47);
x_49 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_1, x_3, x_4, x_35);
x_50 = lean_array_uset(x_48, x_34, x_49);
lean_ctor_set(x_7, 1, x_50);
x_15 = x_7;
goto block_18;
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_14);
lean_ctor_set(x_16, 3, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_61; uint64_t x_62; lean_object* x_63; uint64_t x_64; uint64_t x_65; uint64_t x_66; lean_object* x_67; uint64_t x_68; uint64_t x_69; uint64_t x_70; size_t x_71; size_t x_72; lean_object* x_73; size_t x_74; size_t x_75; size_t x_76; lean_object* x_77; uint8_t x_78; 
x_51 = lean_ctor_get(x_7, 0);
x_52 = lean_ctor_get(x_7, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_7);
x_53 = lean_box(0);
x_54 = lean_ctor_get(x_6, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_6, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_6, 2);
lean_inc(x_56);
lean_dec(x_6);
x_61 = lean_array_get_size(x_52);
x_62 = l_Lean_Expr_hash(x_3);
x_63 = lean_unsigned_to_nat(32u);
x_64 = lean_uint64_of_nat(x_63);
x_65 = lean_uint64_shift_right(x_62, x_64);
x_66 = lean_uint64_xor(x_62, x_65);
x_67 = lean_unsigned_to_nat(16u);
x_68 = lean_uint64_of_nat(x_67);
x_69 = lean_uint64_shift_right(x_66, x_68);
x_70 = lean_uint64_xor(x_66, x_69);
x_71 = lean_uint64_to_usize(x_70);
x_72 = lean_usize_of_nat(x_61);
lean_dec(x_61);
x_73 = lean_unsigned_to_nat(1u);
x_74 = lean_usize_of_nat(x_73);
x_75 = lean_usize_sub(x_72, x_74);
x_76 = lean_usize_land(x_71, x_75);
x_77 = lean_array_uget(x_52, x_76);
lean_inc(x_77);
lean_inc(x_3);
lean_inc(x_1);
x_78 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_1, x_3, x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
lean_dec(x_1);
x_79 = lean_nat_add(x_51, x_73);
lean_dec(x_51);
x_80 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_80, 0, x_3);
lean_ctor_set(x_80, 1, x_4);
lean_ctor_set(x_80, 2, x_77);
x_81 = lean_array_uset(x_52, x_76, x_80);
x_82 = lean_unsigned_to_nat(2u);
x_83 = lean_nat_shiftl(x_79, x_82);
x_84 = lean_unsigned_to_nat(3u);
x_85 = lean_nat_div(x_83, x_84);
lean_dec(x_83);
x_86 = lean_array_get_size(x_81);
x_87 = lean_nat_dec_le(x_85, x_86);
lean_dec(x_86);
lean_dec(x_85);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_2, x_81);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_79);
lean_ctor_set(x_89, 1, x_88);
x_57 = x_89;
goto block_60;
}
else
{
lean_object* x_90; 
lean_dec(x_2);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_79);
lean_ctor_set(x_90, 1, x_81);
x_57 = x_90;
goto block_60;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_2);
x_91 = lean_box(0);
x_92 = lean_array_uset(x_52, x_76, x_91);
x_93 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_1, x_3, x_4, x_77);
x_94 = lean_array_uset(x_92, x_76, x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_51);
lean_ctor_set(x_95, 1, x_94);
x_57 = x_95;
goto block_60;
}
block_60:
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_58, 0, x_54);
lean_ctor_set(x_58, 1, x_55);
lean_ctor_set(x_58, 2, x_56);
lean_ctor_set(x_58, 3, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
static lean_object* _init_l_Lean_MetavarContext_LevelMVarToParam_instMonadCacheExprStructEqExprM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_ExprStructEq_instBEq;
x_2 = lean_alloc_closure((void*)(l_Lean_MetavarContext_LevelMVarToParam_instMonadCacheExprStructEqExprM___lam__0___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_ExprStructEq_hash___boxed), 1, 0);
x_4 = lean_alloc_closure((void*)(l_Lean_MetavarContext_LevelMVarToParam_instMonadCacheExprStructEqExprM___lam__1___boxed), 6, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_LevelMVarToParam_instMonadCacheExprStructEqExprM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MetavarContext_LevelMVarToParam_instMonadCacheExprStructEqExprM___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_LevelMVarToParam_instMonadCacheExprStructEqExprM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MetavarContext_LevelMVarToParam_instMonadCacheExprStructEqExprM___lam__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_LevelMVarToParam_mkParamName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_inc(x_4);
x_5 = lean_name_append_index_after(x_3, x_4);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
x_7 = lean_apply_1(x_6, x_5);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_5);
x_11 = lean_array_push(x_10, x_5);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_14 = lean_ctor_get(x_2, 3);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_13);
lean_ctor_set(x_15, 3, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_5);
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_4, x_19);
lean_dec(x_4);
x_21 = lean_ctor_get(x_2, 3);
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set(x_22, 3, x_21);
x_2 = x_22;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___Lean_MetavarContext_LevelMVarToParam_visitLevel_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_4 = lean_box(0);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 4);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 5);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 6);
lean_inc(x_12);
x_13 = l_Lean_PersistentHashMap_insert___at___Lean_assignLevelMVarExp_spec__0___redArg(x_12, x_1, x_2);
x_14 = lean_ctor_get(x_5, 7);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 8);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_7);
lean_ctor_set(x_16, 2, x_8);
lean_ctor_set(x_16, 3, x_9);
lean_ctor_set(x_16, 4, x_10);
lean_ctor_set(x_16, 5, x_11);
lean_ctor_set(x_16, 6, x_13);
lean_ctor_set(x_16, 7, x_14);
lean_ctor_set(x_16, 8, x_15);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_3, 3);
lean_inc(x_19);
lean_dec(x_3);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_18);
lean_ctor_set(x_20, 3, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___Lean_MetavarContext_LevelMVarToParam_visitLevel_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_assignLevelMVar___at___Lean_MetavarContext_LevelMVarToParam_visitLevel_spec__0___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_LevelMVarToParam_visitLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_inc(x_4);
x_5 = l_Lean_MetavarContext_LevelMVarToParam_visitLevel(x_4, x_2, x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ptr_addr(x_4);
lean_dec(x_4);
x_9 = lean_ptr_addr(x_7);
x_10 = lean_usize_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = l_Lean_Level_succ___override(x_7);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_dec(x_7);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
}
else
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_14 = lean_ptr_addr(x_4);
lean_dec(x_4);
x_15 = lean_ptr_addr(x_12);
x_16 = lean_usize_dec_eq(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_17 = l_Lean_Level_succ___override(x_12);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_12);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_13);
return x_19;
}
}
}
case 2:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; size_t x_35; size_t x_36; uint8_t x_37; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_2);
lean_inc(x_20);
x_22 = l_Lean_MetavarContext_LevelMVarToParam_visitLevel(x_20, x_2, x_3);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_21);
x_25 = l_Lean_MetavarContext_LevelMVarToParam_visitLevel(x_21, x_2, x_24);
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
x_35 = lean_ptr_addr(x_20);
lean_dec(x_20);
x_36 = lean_ptr_addr(x_23);
x_37 = lean_usize_dec_eq(x_35, x_36);
if (x_37 == 0)
{
lean_dec(x_21);
x_29 = x_37;
goto block_34;
}
else
{
size_t x_38; size_t x_39; uint8_t x_40; 
x_38 = lean_ptr_addr(x_21);
lean_dec(x_21);
x_39 = lean_ptr_addr(x_26);
x_40 = lean_usize_dec_eq(x_38, x_39);
x_29 = x_40;
goto block_34;
}
block_34:
{
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_1);
x_30 = l_Lean_mkLevelMax_x27(x_23, x_26);
if (lean_is_scalar(x_28)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_28;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_simpLevelMax_x27(x_23, x_26, x_1);
lean_dec(x_1);
lean_dec(x_26);
lean_dec(x_23);
if (lean_is_scalar(x_28)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_28;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_27);
return x_33;
}
}
}
case 3:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; size_t x_56; size_t x_57; uint8_t x_58; 
x_41 = lean_ctor_get(x_1, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_1, 1);
lean_inc(x_42);
lean_inc(x_2);
lean_inc(x_41);
x_43 = l_Lean_MetavarContext_LevelMVarToParam_visitLevel(x_41, x_2, x_3);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_42);
x_46 = l_Lean_MetavarContext_LevelMVarToParam_visitLevel(x_42, x_2, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_56 = lean_ptr_addr(x_41);
lean_dec(x_41);
x_57 = lean_ptr_addr(x_44);
x_58 = lean_usize_dec_eq(x_56, x_57);
if (x_58 == 0)
{
lean_dec(x_42);
x_50 = x_58;
goto block_55;
}
else
{
size_t x_59; size_t x_60; uint8_t x_61; 
x_59 = lean_ptr_addr(x_42);
lean_dec(x_42);
x_60 = lean_ptr_addr(x_47);
x_61 = lean_usize_dec_eq(x_59, x_60);
x_50 = x_61;
goto block_55;
}
block_55:
{
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_1);
x_51 = l_Lean_mkLevelIMax_x27(x_44, x_47);
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
lean_object* x_53; lean_object* x_54; 
x_53 = l_Lean_simpLevelIMax_x27(x_44, x_47, x_1);
lean_dec(x_1);
if (lean_is_scalar(x_49)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_49;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_48);
return x_54;
}
}
}
case 5:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_1, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_3, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_63, 6);
lean_inc(x_64);
lean_dec(x_63);
x_65 = l_Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0___redArg(x_64, x_62);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_2, 2);
lean_inc(x_66);
lean_inc(x_62);
x_67 = lean_apply_1(x_66, x_62);
x_68 = lean_unbox(x_67);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_dec(x_1);
x_69 = l_Lean_MetavarContext_LevelMVarToParam_mkParamName(x_2, x_3);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Lean_Level_param___override(x_70);
lean_inc(x_72);
x_73 = l_Lean_assignLevelMVar___at___Lean_MetavarContext_LevelMVarToParam_visitLevel_spec__0___redArg(x_62, x_72, x_71);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_73, 0);
lean_dec(x_75);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_72);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
else
{
lean_object* x_78; 
lean_dec(x_62);
lean_dec(x_2);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_1);
lean_ctor_set(x_78, 1, x_3);
return x_78;
}
}
else
{
lean_object* x_79; 
lean_dec(x_62);
lean_dec(x_1);
x_79 = lean_ctor_get(x_65, 0);
lean_inc(x_79);
lean_dec(x_65);
x_1 = x_79;
goto _start;
}
}
default: 
{
lean_object* x_81; 
lean_dec(x_2);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_1);
lean_ctor_set(x_81, 1, x_3);
return x_81;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___Lean_MetavarContext_LevelMVarToParam_visitLevel_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_assignLevelMVar___at___Lean_MetavarContext_LevelMVarToParam_visitLevel_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___Lean_MetavarContext_LevelMVarToParam_main_visitApp_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = l_Lean_MetavarContext_getExprAssignmentCore_x3f(x_3, x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___Lean_MetavarContext_LevelMVarToParam_main_visitApp_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getExprMVarAssignment_x3f___at___Lean_MetavarContext_LevelMVarToParam_main_visitApp_spec__0___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_MetavarContext_LevelMVarToParam_main_visitApp_spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_2, x_1);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_8 = lean_array_uget(x_3, x_2);
lean_inc(x_4);
x_9 = l_Lean_MetavarContext_LevelMVarToParam_main(x_8, x_4, x_5);
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
LEAN_EXPORT lean_object* l_Lean_MetavarContext_LevelMVarToParam_main_visitApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = l_Lean_getExprMVarAssignment_x3f___at___Lean_MetavarContext_LevelMVarToParam_main_visitApp_spec__0___redArg(x_5, x_4);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; size_t x_9; lean_object* x_10; size_t x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_array_size(x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_usize_of_nat(x_10);
x_12 = l_Array_mapMUnsafe_map___at___Lean_MetavarContext_LevelMVarToParam_main_visitApp_spec__1(x_9, x_11, x_2, x_3, x_8);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l_Lean_mkAppN(x_1, x_14);
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
x_18 = l_Lean_mkAppN(x_1, x_16);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_1);
x_20 = lean_ctor_get(x_6, 1);
lean_inc(x_20);
lean_dec(x_6);
x_21 = lean_ctor_get(x_7, 0);
lean_inc(x_21);
lean_dec(x_7);
x_22 = l_Lean_MetavarContext_LevelMVarToParam_main_visitApp(x_21, x_2, x_3, x_20);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = l_Lean_Expr_headBeta(x_24);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_28 = l_Lean_Expr_headBeta(x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; lean_object* x_34; size_t x_35; lean_object* x_36; uint8_t x_37; 
lean_inc(x_3);
x_30 = l_Lean_MetavarContext_LevelMVarToParam_main(x_1, x_3, x_4);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_array_size(x_2);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_usize_of_nat(x_34);
x_36 = l_Array_mapMUnsafe_map___at___Lean_MetavarContext_LevelMVarToParam_main_visitApp_spec__1(x_33, x_35, x_2, x_3, x_32);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = l_Lean_mkAppN(x_31, x_38);
lean_dec(x_38);
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
x_42 = l_Lean_mkAppN(x_31, x_40);
lean_dec(x_40);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_MetavarContext_LevelMVarToParam_main_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
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
lean_inc(x_3);
x_10 = l_Lean_MetavarContext_LevelMVarToParam_visitLevel(x_8, x_3, x_4);
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
lean_inc(x_3);
x_16 = l_Lean_MetavarContext_LevelMVarToParam_visitLevel(x_14, x_3, x_4);
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_MetavarContext_LevelMVarToParam_main_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_array_set(x_2, x_3, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_3, x_9);
lean_dec(x_3);
x_1 = x_6;
x_2 = x_8;
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_12; 
lean_dec(x_3);
x_12 = l_Lean_MetavarContext_LevelMVarToParam_main_visitApp(x_1, x_2, x_4, x_5);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_LevelMVarToParam_main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_12; 
x_12 = l_Lean_Expr_hasMVar(x_1);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_3, 3);
lean_inc(x_14);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; lean_object* x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; lean_object* x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; size_t x_28; size_t x_29; lean_object* x_30; size_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_90; size_t x_94; size_t x_95; lean_object* x_96; lean_object* x_97; 
x_16 = lean_ctor_get(x_14, 1);
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = lean_array_get_size(x_16);
x_19 = l_Lean_Expr_hash(x_1);
x_20 = lean_unsigned_to_nat(32u);
x_21 = lean_uint64_of_nat(x_20);
x_22 = lean_uint64_shift_right(x_19, x_21);
x_23 = lean_uint64_xor(x_19, x_22);
x_24 = lean_unsigned_to_nat(16u);
x_25 = lean_uint64_of_nat(x_24);
x_26 = lean_uint64_shift_right(x_23, x_25);
x_27 = lean_uint64_xor(x_23, x_26);
x_28 = lean_uint64_to_usize(x_27);
x_29 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_usize_of_nat(x_30);
x_94 = lean_usize_sub(x_29, x_31);
x_95 = lean_usize_land(x_28, x_94);
x_96 = lean_array_uget(x_16, x_95);
lean_dec(x_16);
x_97 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__0___redArg(x_1, x_96);
lean_dec(x_96);
if (lean_obj_tag(x_97) == 0)
{
lean_free_object(x_14);
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_unsigned_to_nat(0u);
x_99 = lean_mk_empty_array_with_capacity(x_98);
lean_inc(x_1);
x_100 = l_Lean_MetavarContext_LevelMVarToParam_main_visitApp(x_1, x_99, x_2, x_3);
x_90 = x_100;
goto block_93;
}
case 3:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; size_t x_105; size_t x_106; uint8_t x_107; 
x_101 = lean_ctor_get(x_1, 0);
lean_inc(x_101);
lean_inc(x_101);
x_102 = l_Lean_MetavarContext_LevelMVarToParam_visitLevel(x_101, x_2, x_3);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_ptr_addr(x_101);
lean_dec(x_101);
x_106 = lean_ptr_addr(x_103);
x_107 = lean_usize_dec_eq(x_105, x_106);
if (x_107 == 0)
{
lean_object* x_108; 
x_108 = l_Lean_Expr_sort___override(x_103);
x_32 = x_108;
x_33 = x_104;
goto block_89;
}
else
{
lean_dec(x_103);
lean_inc(x_1);
x_32 = x_1;
x_33 = x_104;
goto block_89;
}
}
case 4:
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_109 = lean_ctor_get(x_1, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_1, 1);
lean_inc(x_110);
x_111 = lean_box(0);
lean_inc(x_110);
x_112 = l_List_mapM_loop___at___Lean_MetavarContext_LevelMVarToParam_main_spec__0(x_110, x_111, x_2, x_3);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = l_ptrEqList___redArg(x_110, x_113);
lean_dec(x_110);
if (x_115 == 0)
{
if (x_12 == 0)
{
lean_dec(x_113);
lean_dec(x_109);
lean_inc(x_1);
x_32 = x_1;
x_33 = x_114;
goto block_89;
}
else
{
lean_object* x_116; 
x_116 = l_Lean_Expr_const___override(x_109, x_113);
x_32 = x_116;
x_33 = x_114;
goto block_89;
}
}
else
{
if (x_12 == 0)
{
lean_object* x_117; 
x_117 = l_Lean_Expr_const___override(x_109, x_113);
x_32 = x_117;
x_33 = x_114;
goto block_89;
}
else
{
lean_dec(x_113);
lean_dec(x_109);
lean_inc(x_1);
x_32 = x_1;
x_33 = x_114;
goto block_89;
}
}
}
case 5:
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_118 = lean_box(0);
x_119 = l_Lean_Expr_sort___override(x_118);
x_120 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_120);
x_121 = lean_mk_array(x_120, x_119);
x_122 = lean_nat_sub(x_120, x_30);
lean_dec(x_120);
lean_inc(x_1);
x_123 = l_Lean_Expr_withAppAux___at___Lean_MetavarContext_LevelMVarToParam_main_spec__1(x_1, x_121, x_122, x_2, x_3);
x_90 = x_123;
goto block_93;
}
case 6:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_124 = lean_ctor_get(x_1, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_1, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_1, 2);
lean_inc(x_126);
x_127 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_inc(x_2);
lean_inc(x_125);
x_128 = l_Lean_MetavarContext_LevelMVarToParam_main(x_125, x_2, x_3);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
lean_inc(x_126);
x_131 = l_Lean_MetavarContext_LevelMVarToParam_main(x_126, x_2, x_130);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = l_Lean_Expr_lam___override(x_124, x_125, x_126, x_127);
if (lean_obj_tag(x_134) == 6)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; uint8_t x_139; size_t x_144; size_t x_145; uint8_t x_146; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_134, 2);
lean_inc(x_137);
x_138 = lean_ctor_get_uint8(x_134, sizeof(void*)*3 + 8);
x_144 = lean_ptr_addr(x_136);
lean_dec(x_136);
x_145 = lean_ptr_addr(x_129);
x_146 = lean_usize_dec_eq(x_144, x_145);
if (x_146 == 0)
{
lean_dec(x_137);
x_139 = x_146;
goto block_143;
}
else
{
size_t x_147; size_t x_148; uint8_t x_149; 
x_147 = lean_ptr_addr(x_137);
lean_dec(x_137);
x_148 = lean_ptr_addr(x_132);
x_149 = lean_usize_dec_eq(x_147, x_148);
x_139 = x_149;
goto block_143;
}
block_143:
{
if (x_139 == 0)
{
lean_object* x_140; 
lean_dec(x_134);
x_140 = l_Lean_Expr_lam___override(x_135, x_129, x_132, x_127);
x_32 = x_140;
x_33 = x_133;
goto block_89;
}
else
{
uint8_t x_141; 
x_141 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_138, x_127);
if (x_141 == 0)
{
lean_object* x_142; 
lean_dec(x_134);
x_142 = l_Lean_Expr_lam___override(x_135, x_129, x_132, x_127);
x_32 = x_142;
x_33 = x_133;
goto block_89;
}
else
{
lean_dec(x_135);
lean_dec(x_132);
lean_dec(x_129);
x_32 = x_134;
x_33 = x_133;
goto block_89;
}
}
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_134);
lean_dec(x_132);
lean_dec(x_129);
x_150 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_151 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateLambda!Impl", 48, 48);
x_152 = lean_unsigned_to_nat(1848u);
x_153 = lean_unsigned_to_nat(19u);
x_154 = lean_mk_string_unchecked("lambda expected", 15, 15);
x_155 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_150, x_151, x_152, x_153, x_154);
lean_dec(x_154);
lean_dec(x_151);
lean_dec(x_150);
x_156 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_155);
x_32 = x_156;
x_33 = x_133;
goto block_89;
}
}
case 7:
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_157 = lean_ctor_get(x_1, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_1, 1);
lean_inc(x_158);
x_159 = lean_ctor_get(x_1, 2);
lean_inc(x_159);
x_160 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_inc(x_2);
lean_inc(x_158);
x_161 = l_Lean_MetavarContext_LevelMVarToParam_main(x_158, x_2, x_3);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
lean_inc(x_159);
x_164 = l_Lean_MetavarContext_LevelMVarToParam_main(x_159, x_2, x_163);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_167 = l_Lean_Expr_forallE___override(x_157, x_158, x_159, x_160);
if (lean_obj_tag(x_167) == 7)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; uint8_t x_172; size_t x_177; size_t x_178; uint8_t x_179; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_167, 2);
lean_inc(x_170);
x_171 = lean_ctor_get_uint8(x_167, sizeof(void*)*3 + 8);
x_177 = lean_ptr_addr(x_169);
lean_dec(x_169);
x_178 = lean_ptr_addr(x_162);
x_179 = lean_usize_dec_eq(x_177, x_178);
if (x_179 == 0)
{
lean_dec(x_170);
x_172 = x_179;
goto block_176;
}
else
{
size_t x_180; size_t x_181; uint8_t x_182; 
x_180 = lean_ptr_addr(x_170);
lean_dec(x_170);
x_181 = lean_ptr_addr(x_165);
x_182 = lean_usize_dec_eq(x_180, x_181);
x_172 = x_182;
goto block_176;
}
block_176:
{
if (x_172 == 0)
{
lean_object* x_173; 
lean_dec(x_167);
x_173 = l_Lean_Expr_forallE___override(x_168, x_162, x_165, x_160);
x_32 = x_173;
x_33 = x_166;
goto block_89;
}
else
{
uint8_t x_174; 
x_174 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_171, x_160);
if (x_174 == 0)
{
lean_object* x_175; 
lean_dec(x_167);
x_175 = l_Lean_Expr_forallE___override(x_168, x_162, x_165, x_160);
x_32 = x_175;
x_33 = x_166;
goto block_89;
}
else
{
lean_dec(x_168);
lean_dec(x_165);
lean_dec(x_162);
x_32 = x_167;
x_33 = x_166;
goto block_89;
}
}
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_167);
lean_dec(x_165);
lean_dec(x_162);
x_183 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_184 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateForall!Impl", 48, 48);
x_185 = lean_unsigned_to_nat(1828u);
x_186 = lean_unsigned_to_nat(23u);
x_187 = lean_mk_string_unchecked("forall expected", 15, 15);
x_188 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_183, x_184, x_185, x_186, x_187);
lean_dec(x_187);
lean_dec(x_184);
lean_dec(x_183);
x_189 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_188);
x_32 = x_189;
x_33 = x_166;
goto block_89;
}
}
case 8:
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_206; size_t x_211; size_t x_212; uint8_t x_213; 
x_190 = lean_ctor_get(x_1, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_1, 1);
lean_inc(x_191);
x_192 = lean_ctor_get(x_1, 2);
lean_inc(x_192);
x_193 = lean_ctor_get(x_1, 3);
lean_inc(x_193);
x_194 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
lean_inc(x_2);
lean_inc(x_191);
x_195 = l_Lean_MetavarContext_LevelMVarToParam_main(x_191, x_2, x_3);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
lean_inc(x_2);
lean_inc(x_192);
x_198 = l_Lean_MetavarContext_LevelMVarToParam_main(x_192, x_2, x_197);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec(x_198);
lean_inc(x_193);
x_201 = l_Lean_MetavarContext_LevelMVarToParam_main(x_193, x_2, x_200);
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
x_211 = lean_ptr_addr(x_191);
lean_dec(x_191);
x_212 = lean_ptr_addr(x_196);
x_213 = lean_usize_dec_eq(x_211, x_212);
if (x_213 == 0)
{
lean_dec(x_192);
x_206 = x_213;
goto block_210;
}
else
{
size_t x_214; size_t x_215; uint8_t x_216; 
x_214 = lean_ptr_addr(x_192);
lean_dec(x_192);
x_215 = lean_ptr_addr(x_199);
x_216 = lean_usize_dec_eq(x_214, x_215);
x_206 = x_216;
goto block_210;
}
block_205:
{
lean_object* x_204; 
x_204 = l_Lean_Expr_letE___override(x_190, x_196, x_199, x_202, x_194);
x_32 = x_204;
x_33 = x_203;
goto block_89;
}
block_210:
{
if (x_206 == 0)
{
lean_dec(x_193);
goto block_205;
}
else
{
size_t x_207; size_t x_208; uint8_t x_209; 
x_207 = lean_ptr_addr(x_193);
lean_dec(x_193);
x_208 = lean_ptr_addr(x_202);
x_209 = lean_usize_dec_eq(x_207, x_208);
if (x_209 == 0)
{
goto block_205;
}
else
{
lean_dec(x_202);
lean_dec(x_199);
lean_dec(x_196);
lean_dec(x_190);
lean_inc(x_1);
x_32 = x_1;
x_33 = x_203;
goto block_89;
}
}
}
}
case 10:
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; size_t x_222; size_t x_223; uint8_t x_224; 
x_217 = lean_ctor_get(x_1, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_1, 1);
lean_inc(x_218);
lean_inc(x_218);
x_219 = l_Lean_MetavarContext_LevelMVarToParam_main(x_218, x_2, x_3);
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
x_222 = lean_ptr_addr(x_218);
lean_dec(x_218);
x_223 = lean_ptr_addr(x_220);
x_224 = lean_usize_dec_eq(x_222, x_223);
if (x_224 == 0)
{
lean_object* x_225; 
x_225 = l_Lean_Expr_mdata___override(x_217, x_220);
x_32 = x_225;
x_33 = x_221;
goto block_89;
}
else
{
lean_dec(x_220);
lean_dec(x_217);
lean_inc(x_1);
x_32 = x_1;
x_33 = x_221;
goto block_89;
}
}
case 11:
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; size_t x_232; size_t x_233; uint8_t x_234; 
x_226 = lean_ctor_get(x_1, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_1, 1);
lean_inc(x_227);
x_228 = lean_ctor_get(x_1, 2);
lean_inc(x_228);
lean_inc(x_228);
x_229 = l_Lean_MetavarContext_LevelMVarToParam_main(x_228, x_2, x_3);
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
lean_dec(x_229);
x_232 = lean_ptr_addr(x_228);
lean_dec(x_228);
x_233 = lean_ptr_addr(x_230);
x_234 = lean_usize_dec_eq(x_232, x_233);
if (x_234 == 0)
{
lean_object* x_235; 
x_235 = l_Lean_Expr_proj___override(x_226, x_227, x_230);
x_32 = x_235;
x_33 = x_231;
goto block_89;
}
else
{
lean_dec(x_230);
lean_dec(x_227);
lean_dec(x_226);
lean_inc(x_1);
x_32 = x_1;
x_33 = x_231;
goto block_89;
}
}
default: 
{
lean_dec(x_2);
lean_inc(x_1);
x_32 = x_1;
x_33 = x_3;
goto block_89;
}
}
}
else
{
lean_object* x_236; 
lean_dec(x_2);
lean_dec(x_1);
x_236 = lean_ctor_get(x_97, 0);
lean_inc(x_236);
lean_dec(x_97);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 0, x_236);
return x_14;
}
block_89:
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_33, 3);
lean_inc(x_34);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; size_t x_43; size_t x_44; lean_object* x_45; uint8_t x_46; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
x_38 = lean_ctor_get(x_33, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_33, 2);
lean_inc(x_40);
lean_dec(x_33);
x_41 = lean_array_get_size(x_37);
x_42 = lean_usize_of_nat(x_41);
lean_dec(x_41);
x_43 = lean_usize_sub(x_42, x_31);
x_44 = lean_usize_land(x_28, x_43);
x_45 = lean_array_uget(x_37, x_44);
x_46 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__1___redArg(x_1, x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_47 = lean_nat_add(x_36, x_30);
lean_dec(x_36);
lean_inc(x_32);
x_48 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_32);
lean_ctor_set(x_48, 2, x_45);
x_49 = lean_array_uset(x_37, x_44, x_48);
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
x_56 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2___redArg(x_49);
lean_ctor_set(x_34, 1, x_56);
lean_ctor_set(x_34, 0, x_47);
x_4 = x_39;
x_5 = x_32;
x_6 = x_38;
x_7 = x_40;
x_8 = x_34;
goto block_11;
}
else
{
lean_ctor_set(x_34, 1, x_49);
lean_ctor_set(x_34, 0, x_47);
x_4 = x_39;
x_5 = x_32;
x_6 = x_38;
x_7 = x_40;
x_8 = x_34;
goto block_11;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_box(0);
x_58 = lean_array_uset(x_37, x_44, x_57);
lean_inc(x_32);
x_59 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__5___redArg(x_1, x_32, x_45);
x_60 = lean_array_uset(x_58, x_44, x_59);
lean_ctor_set(x_34, 1, x_60);
x_4 = x_39;
x_5 = x_32;
x_6 = x_38;
x_7 = x_40;
x_8 = x_34;
goto block_11;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; size_t x_67; size_t x_68; size_t x_69; lean_object* x_70; uint8_t x_71; 
x_61 = lean_ctor_get(x_34, 0);
x_62 = lean_ctor_get(x_34, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_34);
x_63 = lean_ctor_get(x_33, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_33, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_33, 2);
lean_inc(x_65);
lean_dec(x_33);
x_66 = lean_array_get_size(x_62);
x_67 = lean_usize_of_nat(x_66);
lean_dec(x_66);
x_68 = lean_usize_sub(x_67, x_31);
x_69 = lean_usize_land(x_28, x_68);
x_70 = lean_array_uget(x_62, x_69);
x_71 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__1___redArg(x_1, x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_72 = lean_nat_add(x_61, x_30);
lean_dec(x_61);
lean_inc(x_32);
x_73 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_73, 0, x_1);
lean_ctor_set(x_73, 1, x_32);
lean_ctor_set(x_73, 2, x_70);
x_74 = lean_array_uset(x_62, x_69, x_73);
x_75 = lean_unsigned_to_nat(2u);
x_76 = lean_nat_shiftl(x_72, x_75);
x_77 = lean_unsigned_to_nat(3u);
x_78 = lean_nat_div(x_76, x_77);
lean_dec(x_76);
x_79 = lean_array_get_size(x_74);
x_80 = lean_nat_dec_le(x_78, x_79);
lean_dec(x_79);
lean_dec(x_78);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2___redArg(x_74);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_72);
lean_ctor_set(x_82, 1, x_81);
x_4 = x_64;
x_5 = x_32;
x_6 = x_63;
x_7 = x_65;
x_8 = x_82;
goto block_11;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_72);
lean_ctor_set(x_83, 1, x_74);
x_4 = x_64;
x_5 = x_32;
x_6 = x_63;
x_7 = x_65;
x_8 = x_83;
goto block_11;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_84 = lean_box(0);
x_85 = lean_array_uset(x_62, x_69, x_84);
lean_inc(x_32);
x_86 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__5___redArg(x_1, x_32, x_70);
x_87 = lean_array_uset(x_85, x_69, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_61);
lean_ctor_set(x_88, 1, x_87);
x_4 = x_64;
x_5 = x_32;
x_6 = x_63;
x_7 = x_65;
x_8 = x_88;
goto block_11;
}
}
}
block_93:
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_32 = x_91;
x_33 = x_92;
goto block_89;
}
}
else
{
lean_object* x_237; lean_object* x_238; uint64_t x_239; lean_object* x_240; uint64_t x_241; uint64_t x_242; uint64_t x_243; lean_object* x_244; uint64_t x_245; uint64_t x_246; uint64_t x_247; size_t x_248; size_t x_249; lean_object* x_250; size_t x_251; lean_object* x_252; lean_object* x_253; lean_object* x_285; size_t x_289; size_t x_290; lean_object* x_291; lean_object* x_292; 
x_237 = lean_ctor_get(x_14, 1);
lean_inc(x_237);
lean_dec(x_14);
x_238 = lean_array_get_size(x_237);
x_239 = l_Lean_Expr_hash(x_1);
x_240 = lean_unsigned_to_nat(32u);
x_241 = lean_uint64_of_nat(x_240);
x_242 = lean_uint64_shift_right(x_239, x_241);
x_243 = lean_uint64_xor(x_239, x_242);
x_244 = lean_unsigned_to_nat(16u);
x_245 = lean_uint64_of_nat(x_244);
x_246 = lean_uint64_shift_right(x_243, x_245);
x_247 = lean_uint64_xor(x_243, x_246);
x_248 = lean_uint64_to_usize(x_247);
x_249 = lean_usize_of_nat(x_238);
lean_dec(x_238);
x_250 = lean_unsigned_to_nat(1u);
x_251 = lean_usize_of_nat(x_250);
x_289 = lean_usize_sub(x_249, x_251);
x_290 = lean_usize_land(x_248, x_289);
x_291 = lean_array_uget(x_237, x_290);
lean_dec(x_237);
x_292 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__0___redArg(x_1, x_291);
lean_dec(x_291);
if (lean_obj_tag(x_292) == 0)
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_293 = lean_unsigned_to_nat(0u);
x_294 = lean_mk_empty_array_with_capacity(x_293);
lean_inc(x_1);
x_295 = l_Lean_MetavarContext_LevelMVarToParam_main_visitApp(x_1, x_294, x_2, x_3);
x_285 = x_295;
goto block_288;
}
case 3:
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; size_t x_300; size_t x_301; uint8_t x_302; 
x_296 = lean_ctor_get(x_1, 0);
lean_inc(x_296);
lean_inc(x_296);
x_297 = l_Lean_MetavarContext_LevelMVarToParam_visitLevel(x_296, x_2, x_3);
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_297, 1);
lean_inc(x_299);
lean_dec(x_297);
x_300 = lean_ptr_addr(x_296);
lean_dec(x_296);
x_301 = lean_ptr_addr(x_298);
x_302 = lean_usize_dec_eq(x_300, x_301);
if (x_302 == 0)
{
lean_object* x_303; 
x_303 = l_Lean_Expr_sort___override(x_298);
x_252 = x_303;
x_253 = x_299;
goto block_284;
}
else
{
lean_dec(x_298);
lean_inc(x_1);
x_252 = x_1;
x_253 = x_299;
goto block_284;
}
}
case 4:
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; uint8_t x_310; 
x_304 = lean_ctor_get(x_1, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_1, 1);
lean_inc(x_305);
x_306 = lean_box(0);
lean_inc(x_305);
x_307 = l_List_mapM_loop___at___Lean_MetavarContext_LevelMVarToParam_main_spec__0(x_305, x_306, x_2, x_3);
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_307, 1);
lean_inc(x_309);
lean_dec(x_307);
x_310 = l_ptrEqList___redArg(x_305, x_308);
lean_dec(x_305);
if (x_310 == 0)
{
if (x_12 == 0)
{
lean_dec(x_308);
lean_dec(x_304);
lean_inc(x_1);
x_252 = x_1;
x_253 = x_309;
goto block_284;
}
else
{
lean_object* x_311; 
x_311 = l_Lean_Expr_const___override(x_304, x_308);
x_252 = x_311;
x_253 = x_309;
goto block_284;
}
}
else
{
if (x_12 == 0)
{
lean_object* x_312; 
x_312 = l_Lean_Expr_const___override(x_304, x_308);
x_252 = x_312;
x_253 = x_309;
goto block_284;
}
else
{
lean_dec(x_308);
lean_dec(x_304);
lean_inc(x_1);
x_252 = x_1;
x_253 = x_309;
goto block_284;
}
}
}
case 5:
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_313 = lean_box(0);
x_314 = l_Lean_Expr_sort___override(x_313);
x_315 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_315);
x_316 = lean_mk_array(x_315, x_314);
x_317 = lean_nat_sub(x_315, x_250);
lean_dec(x_315);
lean_inc(x_1);
x_318 = l_Lean_Expr_withAppAux___at___Lean_MetavarContext_LevelMVarToParam_main_spec__1(x_1, x_316, x_317, x_2, x_3);
x_285 = x_318;
goto block_288;
}
case 6:
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_319 = lean_ctor_get(x_1, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_1, 1);
lean_inc(x_320);
x_321 = lean_ctor_get(x_1, 2);
lean_inc(x_321);
x_322 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_inc(x_2);
lean_inc(x_320);
x_323 = l_Lean_MetavarContext_LevelMVarToParam_main(x_320, x_2, x_3);
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_323, 1);
lean_inc(x_325);
lean_dec(x_323);
lean_inc(x_321);
x_326 = l_Lean_MetavarContext_LevelMVarToParam_main(x_321, x_2, x_325);
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_326, 1);
lean_inc(x_328);
lean_dec(x_326);
x_329 = l_Lean_Expr_lam___override(x_319, x_320, x_321, x_322);
if (lean_obj_tag(x_329) == 6)
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; uint8_t x_333; uint8_t x_334; size_t x_339; size_t x_340; uint8_t x_341; 
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_329, 1);
lean_inc(x_331);
x_332 = lean_ctor_get(x_329, 2);
lean_inc(x_332);
x_333 = lean_ctor_get_uint8(x_329, sizeof(void*)*3 + 8);
x_339 = lean_ptr_addr(x_331);
lean_dec(x_331);
x_340 = lean_ptr_addr(x_324);
x_341 = lean_usize_dec_eq(x_339, x_340);
if (x_341 == 0)
{
lean_dec(x_332);
x_334 = x_341;
goto block_338;
}
else
{
size_t x_342; size_t x_343; uint8_t x_344; 
x_342 = lean_ptr_addr(x_332);
lean_dec(x_332);
x_343 = lean_ptr_addr(x_327);
x_344 = lean_usize_dec_eq(x_342, x_343);
x_334 = x_344;
goto block_338;
}
block_338:
{
if (x_334 == 0)
{
lean_object* x_335; 
lean_dec(x_329);
x_335 = l_Lean_Expr_lam___override(x_330, x_324, x_327, x_322);
x_252 = x_335;
x_253 = x_328;
goto block_284;
}
else
{
uint8_t x_336; 
x_336 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_333, x_322);
if (x_336 == 0)
{
lean_object* x_337; 
lean_dec(x_329);
x_337 = l_Lean_Expr_lam___override(x_330, x_324, x_327, x_322);
x_252 = x_337;
x_253 = x_328;
goto block_284;
}
else
{
lean_dec(x_330);
lean_dec(x_327);
lean_dec(x_324);
x_252 = x_329;
x_253 = x_328;
goto block_284;
}
}
}
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
lean_dec(x_329);
lean_dec(x_327);
lean_dec(x_324);
x_345 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_346 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateLambda!Impl", 48, 48);
x_347 = lean_unsigned_to_nat(1848u);
x_348 = lean_unsigned_to_nat(19u);
x_349 = lean_mk_string_unchecked("lambda expected", 15, 15);
x_350 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_345, x_346, x_347, x_348, x_349);
lean_dec(x_349);
lean_dec(x_346);
lean_dec(x_345);
x_351 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_350);
x_252 = x_351;
x_253 = x_328;
goto block_284;
}
}
case 7:
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_352 = lean_ctor_get(x_1, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_1, 1);
lean_inc(x_353);
x_354 = lean_ctor_get(x_1, 2);
lean_inc(x_354);
x_355 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_inc(x_2);
lean_inc(x_353);
x_356 = l_Lean_MetavarContext_LevelMVarToParam_main(x_353, x_2, x_3);
x_357 = lean_ctor_get(x_356, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_356, 1);
lean_inc(x_358);
lean_dec(x_356);
lean_inc(x_354);
x_359 = l_Lean_MetavarContext_LevelMVarToParam_main(x_354, x_2, x_358);
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_359, 1);
lean_inc(x_361);
lean_dec(x_359);
x_362 = l_Lean_Expr_forallE___override(x_352, x_353, x_354, x_355);
if (lean_obj_tag(x_362) == 7)
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; uint8_t x_366; uint8_t x_367; size_t x_372; size_t x_373; uint8_t x_374; 
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_362, 1);
lean_inc(x_364);
x_365 = lean_ctor_get(x_362, 2);
lean_inc(x_365);
x_366 = lean_ctor_get_uint8(x_362, sizeof(void*)*3 + 8);
x_372 = lean_ptr_addr(x_364);
lean_dec(x_364);
x_373 = lean_ptr_addr(x_357);
x_374 = lean_usize_dec_eq(x_372, x_373);
if (x_374 == 0)
{
lean_dec(x_365);
x_367 = x_374;
goto block_371;
}
else
{
size_t x_375; size_t x_376; uint8_t x_377; 
x_375 = lean_ptr_addr(x_365);
lean_dec(x_365);
x_376 = lean_ptr_addr(x_360);
x_377 = lean_usize_dec_eq(x_375, x_376);
x_367 = x_377;
goto block_371;
}
block_371:
{
if (x_367 == 0)
{
lean_object* x_368; 
lean_dec(x_362);
x_368 = l_Lean_Expr_forallE___override(x_363, x_357, x_360, x_355);
x_252 = x_368;
x_253 = x_361;
goto block_284;
}
else
{
uint8_t x_369; 
x_369 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_366, x_355);
if (x_369 == 0)
{
lean_object* x_370; 
lean_dec(x_362);
x_370 = l_Lean_Expr_forallE___override(x_363, x_357, x_360, x_355);
x_252 = x_370;
x_253 = x_361;
goto block_284;
}
else
{
lean_dec(x_363);
lean_dec(x_360);
lean_dec(x_357);
x_252 = x_362;
x_253 = x_361;
goto block_284;
}
}
}
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
lean_dec(x_362);
lean_dec(x_360);
lean_dec(x_357);
x_378 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_379 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateForall!Impl", 48, 48);
x_380 = lean_unsigned_to_nat(1828u);
x_381 = lean_unsigned_to_nat(23u);
x_382 = lean_mk_string_unchecked("forall expected", 15, 15);
x_383 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_378, x_379, x_380, x_381, x_382);
lean_dec(x_382);
lean_dec(x_379);
lean_dec(x_378);
x_384 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_383);
x_252 = x_384;
x_253 = x_361;
goto block_284;
}
}
case 8:
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; uint8_t x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; uint8_t x_401; size_t x_406; size_t x_407; uint8_t x_408; 
x_385 = lean_ctor_get(x_1, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_1, 1);
lean_inc(x_386);
x_387 = lean_ctor_get(x_1, 2);
lean_inc(x_387);
x_388 = lean_ctor_get(x_1, 3);
lean_inc(x_388);
x_389 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
lean_inc(x_2);
lean_inc(x_386);
x_390 = l_Lean_MetavarContext_LevelMVarToParam_main(x_386, x_2, x_3);
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_390, 1);
lean_inc(x_392);
lean_dec(x_390);
lean_inc(x_2);
lean_inc(x_387);
x_393 = l_Lean_MetavarContext_LevelMVarToParam_main(x_387, x_2, x_392);
x_394 = lean_ctor_get(x_393, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_393, 1);
lean_inc(x_395);
lean_dec(x_393);
lean_inc(x_388);
x_396 = l_Lean_MetavarContext_LevelMVarToParam_main(x_388, x_2, x_395);
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_396, 1);
lean_inc(x_398);
lean_dec(x_396);
x_406 = lean_ptr_addr(x_386);
lean_dec(x_386);
x_407 = lean_ptr_addr(x_391);
x_408 = lean_usize_dec_eq(x_406, x_407);
if (x_408 == 0)
{
lean_dec(x_387);
x_401 = x_408;
goto block_405;
}
else
{
size_t x_409; size_t x_410; uint8_t x_411; 
x_409 = lean_ptr_addr(x_387);
lean_dec(x_387);
x_410 = lean_ptr_addr(x_394);
x_411 = lean_usize_dec_eq(x_409, x_410);
x_401 = x_411;
goto block_405;
}
block_400:
{
lean_object* x_399; 
x_399 = l_Lean_Expr_letE___override(x_385, x_391, x_394, x_397, x_389);
x_252 = x_399;
x_253 = x_398;
goto block_284;
}
block_405:
{
if (x_401 == 0)
{
lean_dec(x_388);
goto block_400;
}
else
{
size_t x_402; size_t x_403; uint8_t x_404; 
x_402 = lean_ptr_addr(x_388);
lean_dec(x_388);
x_403 = lean_ptr_addr(x_397);
x_404 = lean_usize_dec_eq(x_402, x_403);
if (x_404 == 0)
{
goto block_400;
}
else
{
lean_dec(x_397);
lean_dec(x_394);
lean_dec(x_391);
lean_dec(x_385);
lean_inc(x_1);
x_252 = x_1;
x_253 = x_398;
goto block_284;
}
}
}
}
case 10:
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; size_t x_417; size_t x_418; uint8_t x_419; 
x_412 = lean_ctor_get(x_1, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_1, 1);
lean_inc(x_413);
lean_inc(x_413);
x_414 = l_Lean_MetavarContext_LevelMVarToParam_main(x_413, x_2, x_3);
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_414, 1);
lean_inc(x_416);
lean_dec(x_414);
x_417 = lean_ptr_addr(x_413);
lean_dec(x_413);
x_418 = lean_ptr_addr(x_415);
x_419 = lean_usize_dec_eq(x_417, x_418);
if (x_419 == 0)
{
lean_object* x_420; 
x_420 = l_Lean_Expr_mdata___override(x_412, x_415);
x_252 = x_420;
x_253 = x_416;
goto block_284;
}
else
{
lean_dec(x_415);
lean_dec(x_412);
lean_inc(x_1);
x_252 = x_1;
x_253 = x_416;
goto block_284;
}
}
case 11:
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; size_t x_427; size_t x_428; uint8_t x_429; 
x_421 = lean_ctor_get(x_1, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_1, 1);
lean_inc(x_422);
x_423 = lean_ctor_get(x_1, 2);
lean_inc(x_423);
lean_inc(x_423);
x_424 = l_Lean_MetavarContext_LevelMVarToParam_main(x_423, x_2, x_3);
x_425 = lean_ctor_get(x_424, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_424, 1);
lean_inc(x_426);
lean_dec(x_424);
x_427 = lean_ptr_addr(x_423);
lean_dec(x_423);
x_428 = lean_ptr_addr(x_425);
x_429 = lean_usize_dec_eq(x_427, x_428);
if (x_429 == 0)
{
lean_object* x_430; 
x_430 = l_Lean_Expr_proj___override(x_421, x_422, x_425);
x_252 = x_430;
x_253 = x_426;
goto block_284;
}
else
{
lean_dec(x_425);
lean_dec(x_422);
lean_dec(x_421);
lean_inc(x_1);
x_252 = x_1;
x_253 = x_426;
goto block_284;
}
}
default: 
{
lean_dec(x_2);
lean_inc(x_1);
x_252 = x_1;
x_253 = x_3;
goto block_284;
}
}
}
else
{
lean_object* x_431; lean_object* x_432; 
lean_dec(x_2);
lean_dec(x_1);
x_431 = lean_ctor_get(x_292, 0);
lean_inc(x_431);
lean_dec(x_292);
x_432 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_432, 0, x_431);
lean_ctor_set(x_432, 1, x_3);
return x_432;
}
block_284:
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; size_t x_262; size_t x_263; size_t x_264; lean_object* x_265; uint8_t x_266; 
x_254 = lean_ctor_get(x_253, 3);
lean_inc(x_254);
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_254, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_257 = x_254;
} else {
 lean_dec_ref(x_254);
 x_257 = lean_box(0);
}
x_258 = lean_ctor_get(x_253, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_253, 1);
lean_inc(x_259);
x_260 = lean_ctor_get(x_253, 2);
lean_inc(x_260);
lean_dec(x_253);
x_261 = lean_array_get_size(x_256);
x_262 = lean_usize_of_nat(x_261);
lean_dec(x_261);
x_263 = lean_usize_sub(x_262, x_251);
x_264 = lean_usize_land(x_248, x_263);
x_265 = lean_array_uget(x_256, x_264);
x_266 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__1___redArg(x_1, x_265);
if (x_266 == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; 
x_267 = lean_nat_add(x_255, x_250);
lean_dec(x_255);
lean_inc(x_252);
x_268 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_268, 0, x_1);
lean_ctor_set(x_268, 1, x_252);
lean_ctor_set(x_268, 2, x_265);
x_269 = lean_array_uset(x_256, x_264, x_268);
x_270 = lean_unsigned_to_nat(2u);
x_271 = lean_nat_shiftl(x_267, x_270);
x_272 = lean_unsigned_to_nat(3u);
x_273 = lean_nat_div(x_271, x_272);
lean_dec(x_271);
x_274 = lean_array_get_size(x_269);
x_275 = lean_nat_dec_le(x_273, x_274);
lean_dec(x_274);
lean_dec(x_273);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; 
x_276 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2___redArg(x_269);
if (lean_is_scalar(x_257)) {
 x_277 = lean_alloc_ctor(0, 2, 0);
} else {
 x_277 = x_257;
}
lean_ctor_set(x_277, 0, x_267);
lean_ctor_set(x_277, 1, x_276);
x_4 = x_259;
x_5 = x_252;
x_6 = x_258;
x_7 = x_260;
x_8 = x_277;
goto block_11;
}
else
{
lean_object* x_278; 
if (lean_is_scalar(x_257)) {
 x_278 = lean_alloc_ctor(0, 2, 0);
} else {
 x_278 = x_257;
}
lean_ctor_set(x_278, 0, x_267);
lean_ctor_set(x_278, 1, x_269);
x_4 = x_259;
x_5 = x_252;
x_6 = x_258;
x_7 = x_260;
x_8 = x_278;
goto block_11;
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_279 = lean_box(0);
x_280 = lean_array_uset(x_256, x_264, x_279);
lean_inc(x_252);
x_281 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__5___redArg(x_1, x_252, x_265);
x_282 = lean_array_uset(x_280, x_264, x_281);
if (lean_is_scalar(x_257)) {
 x_283 = lean_alloc_ctor(0, 2, 0);
} else {
 x_283 = x_257;
}
lean_ctor_set(x_283, 0, x_255);
lean_ctor_set(x_283, 1, x_282);
x_4 = x_259;
x_5 = x_252;
x_6 = x_258;
x_7 = x_260;
x_8 = x_283;
goto block_11;
}
}
block_288:
{
lean_object* x_286; lean_object* x_287; 
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
lean_dec(x_285);
x_252 = x_286;
x_253 = x_287;
goto block_284;
}
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_9, 2, x_7);
lean_ctor_set(x_9, 3, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___Lean_MetavarContext_LevelMVarToParam_main_visitApp_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getExprMVarAssignment_x3f___at___Lean_MetavarContext_LevelMVarToParam_main_visitApp_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___Lean_MetavarContext_LevelMVarToParam_main_visitApp_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getExprMVarAssignment_x3f___at___Lean_MetavarContext_LevelMVarToParam_main_visitApp_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_MetavarContext_LevelMVarToParam_main_visitApp_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l_Array_mapMUnsafe_map___at___Lean_MetavarContext_LevelMVarToParam_main_visitApp_spec__1(x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_levelMVarToParam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_mk_empty_array_with_capacity(x_8);
x_10 = lean_unsigned_to_nat(8u);
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_nat_shiftl(x_10, x_11);
x_13 = lean_unsigned_to_nat(3u);
x_14 = lean_nat_div(x_12, x_13);
lean_dec(x_12);
x_15 = l_Nat_nextPowerOfTwo(x_14);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = lean_mk_array(x_15, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_9);
lean_ctor_set(x_19, 2, x_6);
lean_ctor_set(x_19, 3, x_18);
x_20 = l_Lean_MetavarContext_LevelMVarToParam_main(x_4, x_7, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 2);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_25);
lean_ctor_set(x_26, 3, x_21);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_getExprAssignmentDomain___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_array_push(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_getExprAssignmentDomain(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_alloc_closure((void*)(l_Lean_MetavarContext_getExprAssignmentDomain___lam__0___boxed), 3, 0);
x_3 = l_Lean_instBEqMVarId;
x_4 = l_Lean_instHashableMVarId;
x_5 = lean_ctor_get(x_1, 7);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_mk_empty_array_with_capacity(x_6);
x_8 = l_Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl_spec__0(lean_box(0), x_3, x_4, lean_box(0), lean_box(0), x_5, x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_getExprAssignmentDomain___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MetavarContext_getExprAssignmentDomain___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MetavarContext_getExprAssignmentDomain___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MetavarContext_getExprAssignmentDomain(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyDecl___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MetavarContext_modifyExprMVarDecl(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyDecl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Lean_MVarId_modifyDecl___redArg___lam__0), 3, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MVarId_modifyDecl___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyLCtx___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MetavarContext_modifyExprMVarLCtx(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyLCtx___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Lean_MVarId_modifyLCtx___redArg___lam__0), 3, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyLCtx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MVarId_modifyLCtx___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarKind___redArg___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MetavarContext_setFVarKind(x_4, x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarKind___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_box(x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_MVarId_setFVarKind___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_3);
lean_closure_set(x_6, 2, x_5);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_1(x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarKind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_MVarId_setFVarKind___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarKind___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lean_MVarId_setFVarKind___redArg___lam__0(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarKind___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_MVarId_setFVarKind___redArg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarKind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_MVarId_setFVarKind(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarBinderInfo___redArg___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MetavarContext_setFVarBinderInfo(x_4, x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarBinderInfo___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_box(x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_MVarId_setFVarBinderInfo___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_3);
lean_closure_set(x_6, 2, x_5);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_1(x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarBinderInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_MVarId_setFVarBinderInfo___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarBinderInfo___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lean_MVarId_setFVarBinderInfo___redArg___lam__0(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarBinderInfo___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_MVarId_setFVarBinderInfo___redArg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarBinderInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_MVarId_setFVarBinderInfo(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
lean_object* initialize_Init_ShareCommon(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_MonadCache(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_LocalContext(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_MetavarContext(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_ShareCommon(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_MonadCache(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_LocalContext(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedLocalInstance = _init_l_Lean_instInhabitedLocalInstance();
lean_mark_persistent(l_Lean_instInhabitedLocalInstance);
l_Lean_instBEqLocalInstance = _init_l_Lean_instBEqLocalInstance();
lean_mark_persistent(l_Lean_instBEqLocalInstance);
l_Lean_instHashableLocalInstance = _init_l_Lean_instHashableLocalInstance();
lean_mark_persistent(l_Lean_instHashableLocalInstance);
l_Lean_instInhabitedMetavarKind = _init_l_Lean_instInhabitedMetavarKind();
l_Lean_instReprMetavarKind = _init_l_Lean_instReprMetavarKind();
lean_mark_persistent(l_Lean_instReprMetavarKind);
l_Lean_instInhabitedMetavarDecl = _init_l_Lean_instInhabitedMetavarDecl();
lean_mark_persistent(l_Lean_instInhabitedMetavarDecl);
l_Lean_instInhabitedMetavarContext = _init_l_Lean_instInhabitedMetavarContext();
lean_mark_persistent(l_Lean_instInhabitedMetavarContext);
l_Lean_instMonadMCtxStateMMetavarContext = _init_l_Lean_instMonadMCtxStateMMetavarContext();
lean_mark_persistent(l_Lean_instMonadMCtxStateMMetavarContext);
l_Lean_DependsOn_instMonadMCtxM = _init_l_Lean_DependsOn_instMonadMCtxM();
lean_mark_persistent(l_Lean_DependsOn_instMonadMCtxM);
l_Lean_MetavarContext_MkBinding_instToStringException = _init_l_Lean_MetavarContext_MkBinding_instToStringException();
lean_mark_persistent(l_Lean_MetavarContext_MkBinding_instToStringException);
l_Lean_MetavarContext_MkBinding_instMonadMCtxM = _init_l_Lean_MetavarContext_MkBinding_instMonadMCtxM();
lean_mark_persistent(l_Lean_MetavarContext_MkBinding_instMonadMCtxM);
l_Lean_MetavarContext_MkBinding_instMonadHashMapCacheAdapterExprStructEqExprM = _init_l_Lean_MetavarContext_MkBinding_instMonadHashMapCacheAdapterExprStructEqExprM();
lean_mark_persistent(l_Lean_MetavarContext_MkBinding_instMonadHashMapCacheAdapterExprStructEqExprM);
l_Lean_MetavarContext_LevelMVarToParam_instMonadMCtxM = _init_l_Lean_MetavarContext_LevelMVarToParam_instMonadMCtxM();
lean_mark_persistent(l_Lean_MetavarContext_LevelMVarToParam_instMonadMCtxM);
l_Lean_MetavarContext_LevelMVarToParam_instMonadCacheExprStructEqExprM = _init_l_Lean_MetavarContext_LevelMVarToParam_instMonadCacheExprStructEqExprM();
lean_mark_persistent(l_Lean_MetavarContext_LevelMVarToParam_instMonadCacheExprStructEqExprM);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
