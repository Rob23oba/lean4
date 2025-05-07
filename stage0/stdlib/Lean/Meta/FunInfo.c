// Lean compiler output
// Module: Lean.Meta.FunInfo
// Imports: Lean.Meta.Basic Lean.Meta.InferType
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5_spec__5_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
extern lean_object* l_Lean_Meta_instBEqInfoCacheKey;
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5_spec__5_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInfo_getArity(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___Array_finIdxOf_x3f___at___Array_idxOf_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__3(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_getOutParamPositions_x3f(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___Array_idxOf_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5_spec__5___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_contains___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkInfoCacheKey___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___Array_finIdxOf_x3f___at___Array_idxOf_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInfo_getArity___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___Array_idxOf_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t l___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_1324_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Array_contains___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__3_spec__3(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5_spec__5(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3_spec__3___redArg___lam__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__3___boxed(lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_instInhabitedEntry(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_Meta_instHashableInfoCacheKey;
size_t lean_usize_shift_left(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3_spec__3___redArg___lam__1___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_qsort_sort___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg___lam__0(lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = l_Lean_Meta_mkInfoCacheKey___redArg(x_1, x_2, x_4, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_5, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = l_Lean_Meta_instBEqInfoCacheKey;
x_17 = l_Lean_Meta_instHashableInfoCacheKey;
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_10);
x_20 = l_Lean_PersistentHashMap_find_x3f___redArg(x_16, x_17, x_19, x_10);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_free_object(x_12);
lean_inc(x_5);
x_21 = lean_apply_5(x_3, x_4, x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_st_ref_take(x_5, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_inc(x_22);
x_31 = l_Lean_PersistentHashMap_insert___redArg(x_16, x_17, x_30, x_10, x_22);
x_32 = lean_ctor_get(x_28, 2);
lean_inc(x_32);
x_33 = lean_ctor_get(x_28, 3);
lean_inc(x_33);
x_34 = lean_ctor_get(x_28, 4);
lean_inc(x_34);
x_35 = lean_ctor_get(x_28, 5);
lean_inc(x_35);
lean_dec(x_28);
x_36 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_31);
lean_ctor_set(x_36, 2, x_32);
lean_ctor_set(x_36, 3, x_33);
lean_ctor_set(x_36, 4, x_34);
lean_ctor_set(x_36, 5, x_35);
x_37 = lean_ctor_get(x_25, 2);
lean_inc(x_37);
x_38 = lean_ctor_get(x_25, 3);
lean_inc(x_38);
x_39 = lean_ctor_get(x_25, 4);
lean_inc(x_39);
lean_dec(x_25);
x_40 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_40, 0, x_27);
lean_ctor_set(x_40, 1, x_36);
lean_ctor_set(x_40, 2, x_37);
lean_ctor_set(x_40, 3, x_38);
lean_ctor_set(x_40, 4, x_39);
x_41 = lean_st_ref_set(x_5, x_40, x_26);
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
lean_ctor_set(x_41, 0, x_22);
return x_41;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_22);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
lean_dec(x_10);
lean_dec(x_5);
return x_21;
}
}
else
{
lean_object* x_46; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_46 = lean_ctor_get(x_20, 0);
lean_inc(x_46);
lean_dec(x_20);
lean_ctor_set(x_12, 0, x_46);
return x_12;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_12, 0);
x_48 = lean_ctor_get(x_12, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_12);
x_49 = l_Lean_Meta_instBEqInfoCacheKey;
x_50 = l_Lean_Meta_instHashableInfoCacheKey;
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
lean_inc(x_10);
x_53 = l_Lean_PersistentHashMap_find_x3f___redArg(x_49, x_50, x_52, x_10);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
lean_inc(x_5);
x_54 = lean_apply_5(x_3, x_4, x_5, x_6, x_7, x_48);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_st_ref_take(x_5, x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_inc(x_55);
x_64 = l_Lean_PersistentHashMap_insert___redArg(x_49, x_50, x_63, x_10, x_55);
x_65 = lean_ctor_get(x_61, 2);
lean_inc(x_65);
x_66 = lean_ctor_get(x_61, 3);
lean_inc(x_66);
x_67 = lean_ctor_get(x_61, 4);
lean_inc(x_67);
x_68 = lean_ctor_get(x_61, 5);
lean_inc(x_68);
lean_dec(x_61);
x_69 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_69, 0, x_62);
lean_ctor_set(x_69, 1, x_64);
lean_ctor_set(x_69, 2, x_65);
lean_ctor_set(x_69, 3, x_66);
lean_ctor_set(x_69, 4, x_67);
lean_ctor_set(x_69, 5, x_68);
x_70 = lean_ctor_get(x_58, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_58, 3);
lean_inc(x_71);
x_72 = lean_ctor_get(x_58, 4);
lean_inc(x_72);
lean_dec(x_58);
x_73 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_73, 0, x_60);
lean_ctor_set(x_73, 1, x_69);
lean_ctor_set(x_73, 2, x_70);
lean_ctor_set(x_73, 3, x_71);
lean_ctor_set(x_73, 4, x_72);
x_74 = lean_st_ref_set(x_5, x_73, x_59);
lean_dec(x_5);
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
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_55);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
else
{
lean_dec(x_10);
lean_dec(x_5);
return x_54;
}
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_78 = lean_ctor_get(x_53, 0);
lean_inc(x_78);
lean_dec(x_53);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_48);
return x_79;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasFVar(x_1);
if (x_4 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_5; 
x_5 = lean_apply_1(x_3, x_2);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Expr_hasFVar(x_2);
if (x_5 == 0)
{
lean_dec(x_4);
return x_3;
}
else
{
lean_object* x_6; 
x_6 = lean_apply_1(x_4, x_3);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___Array_finIdxOf_x3f___at___Array_idxOf_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___Array_idxOf_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_idxOfAux___at___Array_finIdxOf_x3f___at___Array_idxOf_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0_spec__0(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_finIdxOf_x3f___at___Array_idxOf_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0(x_1, x_2);
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
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Array_contains___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__3_spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
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
LEAN_EXPORT uint8_t l_Array_contains___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__3(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_Array_anyMUnsafe_any___at___Array_contains___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__3_spec__3(x_2, x_1, x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Expr_hasFVar(x_1);
if (x_8 == 0)
{
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(x_3, x_5, x_2);
x_10 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(x_3, x_6, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_4; 
x_4 = l_Array_idxOf_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
return x_3;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Array_contains___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__3(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_push(x_3, x_5);
return x_7;
}
else
{
lean_dec(x_5);
return x_3;
}
}
}
case 5:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = l_Lean_Expr_hasFVar(x_2);
if (x_10 == 0)
{
return x_3;
}
else
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(x_1, x_8, x_3);
x_2 = x_9;
x_3 = x_11;
goto _start;
}
}
case 6:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 2);
x_16 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_17 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___lam__0(x_2, x_3, x_1, x_13, x_14, x_15, x_16);
return x_17;
}
case 7:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
x_20 = lean_ctor_get(x_2, 2);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_22 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___lam__0(x_2, x_3, x_1, x_18, x_19, x_20, x_21);
return x_22;
}
case 8:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
x_25 = lean_ctor_get(x_2, 3);
x_26 = l_Lean_Expr_hasFVar(x_2);
if (x_26 == 0)
{
return x_3;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(x_1, x_23, x_3);
x_28 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(x_1, x_24, x_27);
x_2 = x_25;
x_3 = x_28;
goto _start;
}
}
case 10:
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_2, 1);
x_2 = x_30;
goto _start;
}
case 11:
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_2, 2);
x_2 = x_32;
goto _start;
}
default: 
{
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___Array_finIdxOf_x3f___at___Array_idxOf_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_idxOfAux___at___Array_finIdxOf_x3f___at___Array_idxOf_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___Array_idxOf_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_finIdxOf_x3f___at___Array_idxOf_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_idxOf_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_contains___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Array_contains___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__3_spec__3(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_contains___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_7);
lean_dec(x_7);
x_9 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_qsort_sort___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_lt(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_5 = lean_alloc_closure((void*)(l_Array_qsort_sort___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg___lam__0___boxed), 2, 0);
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
x_10 = l_Array_qsort_sort___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(x_8, x_2, x_7);
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
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_qsort_sort___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(x_1, x_2, x_4);
x_6 = lean_array_get_size(x_5);
x_7 = lean_nat_dec_eq(x_6, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_13; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_6, x_8);
lean_dec(x_6);
x_13 = lean_nat_dec_le(x_3, x_9);
if (x_13 == 0)
{
lean_inc(x_9);
x_10 = x_9;
goto block_12;
}
else
{
x_10 = x_3;
goto block_12;
}
block_12:
{
lean_object* x_11; 
x_11 = l_Array_qsort_sort___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(x_5, x_10, x_9);
lean_dec(x_9);
return x_11;
}
}
else
{
lean_dec(x_6);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_qsort_sort___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsort_sort___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_qsort_sort___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_15; uint8_t x_16; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_3, x_8);
lean_dec(x_3);
x_15 = lean_array_fget(x_2, x_4);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*1 + 1);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = l_Array_contains___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__3(x_1, x_4);
if (x_17 == 0)
{
x_10 = x_15;
goto block_14;
}
else
{
uint8_t x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; 
x_18 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_15, sizeof(void*)*1 + 2);
x_21 = lean_ctor_get_uint8(x_15, sizeof(void*)*1 + 3);
x_22 = lean_ctor_get_uint8(x_15, sizeof(void*)*1 + 4);
x_23 = lean_ctor_get_uint8(x_15, sizeof(void*)*1 + 5);
lean_dec(x_15);
x_24 = lean_alloc_ctor(0, 1, 6);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_18);
lean_ctor_set_uint8(x_24, sizeof(void*)*1 + 1, x_17);
lean_ctor_set_uint8(x_24, sizeof(void*)*1 + 2, x_20);
lean_ctor_set_uint8(x_24, sizeof(void*)*1 + 3, x_21);
lean_ctor_set_uint8(x_24, sizeof(void*)*1 + 4, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*1 + 5, x_23);
x_10 = x_24;
goto block_14;
}
}
else
{
x_10 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_nat_add(x_4, x_8);
lean_dec(x_4);
x_12 = lean_array_push(x_5, x_10);
x_3 = x_9;
x_4 = x_11;
x_5 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_mapFinIdxM_map___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_mk_empty_array_with_capacity(x_6);
x_8 = l_Array_mapFinIdxM_map___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg(x_2, x_1, x_6, x_4, x_7);
return x_8;
}
else
{
lean_inc(x_1);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_mapFinIdxM_map___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_mapFinIdxM_map___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_5, 1);
x_20 = lean_nat_dec_lt(x_7, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_12);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_6, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_6, 1);
lean_inc(x_23);
lean_dec(x_6);
x_24 = l_Array_contains___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__3(x_1, x_7);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_23);
x_13 = x_25;
x_14 = x_12;
goto block_18;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_array_fget(x_2, x_7);
x_27 = l_Array_idxOf_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0(x_3, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
lean_dec(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_23);
x_13 = x_28;
x_14 = x_12;
goto block_18;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_26);
x_30 = lean_infer_type(x_26, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_33 = lean_whnf(x_31, x_8, x_9, x_10, x_11, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_41; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_41 = l_Lean_Expr_isForall(x_34);
lean_dec(x_34);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_29);
lean_dec(x_26);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_22);
lean_ctor_set(x_42, 1, x_23);
x_13 = x_42;
x_14 = x_35;
goto block_18;
}
else
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_array_get_size(x_23);
x_44 = lean_nat_dec_lt(x_29, x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_dec(x_29);
x_36 = x_23;
goto block_40;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_45 = lean_array_fget(x_23, x_29);
x_46 = lean_box(0);
x_47 = lean_array_fset(x_23, x_29, x_46);
x_48 = lean_ctor_get_uint8(x_45, sizeof(void*)*1);
x_49 = lean_ctor_get_uint8(x_45, sizeof(void*)*1 + 1);
x_50 = lean_ctor_get(x_45, 0);
lean_inc(x_50);
x_51 = lean_ctor_get_uint8(x_45, sizeof(void*)*1 + 2);
x_52 = lean_ctor_get_uint8(x_45, sizeof(void*)*1 + 3);
x_53 = lean_ctor_get_uint8(x_45, sizeof(void*)*1 + 5);
lean_dec(x_45);
x_54 = lean_alloc_ctor(0, 1, 6);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_48);
lean_ctor_set_uint8(x_54, sizeof(void*)*1 + 1, x_49);
lean_ctor_set_uint8(x_54, sizeof(void*)*1 + 2, x_51);
lean_ctor_set_uint8(x_54, sizeof(void*)*1 + 3, x_52);
lean_ctor_set_uint8(x_54, sizeof(void*)*1 + 4, x_4);
lean_ctor_set_uint8(x_54, sizeof(void*)*1 + 5, x_53);
x_55 = lean_array_fset(x_47, x_29, x_54);
lean_dec(x_29);
x_36 = x_55;
goto block_40;
}
}
block_40:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = l_Lean_Expr_fvarId_x21(x_26);
lean_dec(x_26);
x_38 = l_Lean_FVarIdSet_insert(x_22, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
x_13 = x_39;
x_14 = x_35;
goto block_18;
}
}
else
{
uint8_t x_56; 
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
else
{
uint8_t x_60; 
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_60 = !lean_is_exclusive(x_30);
if (x_60 == 0)
{
return x_30;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_30, 0);
x_62 = lean_ctor_get(x_30, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_30);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
}
block_18:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_5, 2);
x_16 = lean_nat_add(x_7, x_15);
lean_dec(x_7);
x_6 = x_13;
x_7 = x_16;
x_12 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_5, 1);
x_20 = lean_nat_dec_lt(x_7, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_12);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_6, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_6, 1);
lean_inc(x_23);
lean_dec(x_6);
x_24 = l_Array_contains___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__3(x_1, x_7);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_23);
x_13 = x_25;
x_14 = x_12;
goto block_18;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_array_fget(x_2, x_7);
x_27 = l_Array_idxOf_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit_spec__0(x_3, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
lean_dec(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_23);
x_13 = x_28;
x_14 = x_12;
goto block_18;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_26);
x_30 = lean_infer_type(x_26, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_33 = lean_whnf(x_31, x_8, x_9, x_10, x_11, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_41; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_41 = l_Lean_Expr_isForall(x_34);
lean_dec(x_34);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_29);
lean_dec(x_26);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_22);
lean_ctor_set(x_42, 1, x_23);
x_13 = x_42;
x_14 = x_35;
goto block_18;
}
else
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_array_get_size(x_23);
x_44 = lean_nat_dec_lt(x_29, x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_dec(x_29);
x_36 = x_23;
goto block_40;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_45 = lean_array_fget(x_23, x_29);
x_46 = lean_box(0);
x_47 = lean_array_fset(x_23, x_29, x_46);
x_48 = lean_ctor_get_uint8(x_45, sizeof(void*)*1);
x_49 = lean_ctor_get_uint8(x_45, sizeof(void*)*1 + 1);
x_50 = lean_ctor_get(x_45, 0);
lean_inc(x_50);
x_51 = lean_ctor_get_uint8(x_45, sizeof(void*)*1 + 2);
x_52 = lean_ctor_get_uint8(x_45, sizeof(void*)*1 + 3);
x_53 = lean_ctor_get_uint8(x_45, sizeof(void*)*1 + 5);
lean_dec(x_45);
x_54 = lean_alloc_ctor(0, 1, 6);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_48);
lean_ctor_set_uint8(x_54, sizeof(void*)*1 + 1, x_49);
lean_ctor_set_uint8(x_54, sizeof(void*)*1 + 2, x_51);
lean_ctor_set_uint8(x_54, sizeof(void*)*1 + 3, x_52);
lean_ctor_set_uint8(x_54, sizeof(void*)*1 + 4, x_4);
lean_ctor_set_uint8(x_54, sizeof(void*)*1 + 5, x_53);
x_55 = lean_array_fset(x_47, x_29, x_54);
lean_dec(x_29);
x_36 = x_55;
goto block_40;
}
}
block_40:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = l_Lean_Expr_fvarId_x21(x_26);
lean_dec(x_26);
x_38 = l_Lean_FVarIdSet_insert(x_22, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
x_13 = x_39;
x_14 = x_35;
goto block_18;
}
}
else
{
uint8_t x_56; 
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
else
{
uint8_t x_60; 
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_60 = !lean_is_exclusive(x_30);
if (x_60 == 0)
{
return x_30;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_30, 0);
x_62 = lean_ctor_get(x_30, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_30);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
}
block_18:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_5, 2);
x_16 = lean_nat_add(x_7, x_15);
x_17 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_13, x_16, x_8, x_9, x_10, x_11, x_14);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3_spec__3___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_mk_string_unchecked("Decidable", 9, 9);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = l_Lean_Expr_isAppOf(x_2, x_9);
lean_dec(x_9);
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
}
LEAN_EXPORT uint8_t l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3_spec__3___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_isFVar(x_2);
if (x_3 == 0)
{
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Expr_fvarId_x21(x_2);
x_5 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_1, x_4);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
else
{
lean_dec(x_5);
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_2, 1);
x_17 = lean_nat_dec_lt(x_4, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_fget(x_1, x_4);
lean_inc(x_5);
x_20 = l_Lean_Meta_getFVarLocalDecl___redArg(x_19, x_5, x_7, x_8, x_9);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_110; lean_object* x_118; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3_spec__3___redArg___lam__0___boxed), 7, 0);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_ctor_get(x_3, 0);
lean_inc(x_26);
lean_inc(x_26);
x_27 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3_spec__3___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_27, 0, x_26);
x_28 = lean_ctor_get(x_3, 1);
lean_inc(x_28);
lean_dec(x_3);
x_118 = lean_ctor_get(x_21, 3);
lean_inc(x_118);
x_110 = x_118;
goto block_117;
block_109:
{
lean_object* x_32; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_29);
x_32 = l_Lean_Meta_isProp(x_29, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_box(0);
x_36 = lean_unbox(x_35);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_29);
x_37 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1(lean_box(0), x_29, x_23, x_36, x_5, x_6, x_7, x_8, x_34);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(x_28, x_30);
lean_dec(x_28);
x_41 = l_Lean_LocalDecl_binderInfo(x_21);
lean_dec(x_21);
x_42 = lean_alloc_ctor(0, 1, 6);
lean_ctor_set(x_42, 0, x_30);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_41);
x_43 = lean_unbox(x_35);
lean_ctor_set_uint8(x_42, sizeof(void*)*1 + 1, x_43);
x_44 = lean_unbox(x_33);
lean_dec(x_33);
lean_ctor_set_uint8(x_42, sizeof(void*)*1 + 2, x_44);
x_45 = lean_unbox(x_38);
lean_dec(x_38);
lean_ctor_set_uint8(x_42, sizeof(void*)*1 + 3, x_45);
x_46 = lean_unbox(x_35);
lean_ctor_set_uint8(x_42, sizeof(void*)*1 + 4, x_46);
lean_ctor_set_uint8(x_42, sizeof(void*)*1 + 5, x_31);
x_47 = lean_array_push(x_40, x_42);
x_48 = lean_box(3);
x_49 = lean_unbox(x_48);
x_50 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_41, x_49);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_29);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_26);
lean_ctor_set(x_51, 1, x_47);
x_10 = x_51;
x_11 = x_39;
goto block_15;
}
else
{
lean_object* x_52; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_29);
x_52 = l_Lean_Meta_isClass_x3f(x_29, x_5, x_6, x_7, x_8, x_39);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_29);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_26);
lean_ctor_set(x_55, 1, x_47);
x_10 = x_55;
x_11 = x_54;
goto block_15;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_56 = lean_ctor_get(x_52, 1);
lean_inc(x_56);
lean_dec(x_52);
x_57 = lean_ctor_get(x_53, 0);
lean_inc(x_57);
lean_dec(x_53);
x_58 = lean_st_ref_get(x_8, x_56);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_ctor_get(x_58, 1);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_getOutParamPositions_x3f(x_62, x_57);
lean_dec(x_57);
if (lean_obj_tag(x_63) == 0)
{
lean_dec(x_29);
lean_ctor_set(x_58, 1, x_47);
lean_ctor_set(x_58, 0, x_26);
x_10 = x_58;
x_11 = x_61;
goto block_15;
}
else
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec(x_63);
x_65 = l_Array_isEmpty___redArg(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_66 = lean_box(0);
x_67 = l_Lean_Expr_sort___override(x_66);
x_68 = l_Lean_Expr_getAppNumArgs(x_29);
lean_inc(x_68);
x_69 = lean_mk_array(x_68, x_67);
x_70 = lean_nat_sub(x_68, x_25);
lean_dec(x_68);
x_71 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_29, x_69, x_70);
x_72 = lean_array_get_size(x_71);
x_73 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_73, 0, x_24);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_73, 2, x_25);
lean_ctor_set(x_58, 1, x_47);
lean_ctor_set(x_58, 0, x_26);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_74 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg(x_64, x_71, x_1, x_50, x_73, x_58, x_24, x_5, x_6, x_7, x_8, x_61);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_64);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_10 = x_75;
x_11 = x_76;
goto block_15;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_74;
}
}
else
{
lean_dec(x_64);
lean_dec(x_29);
lean_ctor_set(x_58, 1, x_47);
lean_ctor_set(x_58, 0, x_26);
x_10 = x_58;
x_11 = x_61;
goto block_15;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_58, 0);
x_78 = lean_ctor_get(x_58, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_58);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_getOutParamPositions_x3f(x_79, x_57);
lean_dec(x_57);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; 
lean_dec(x_29);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_26);
lean_ctor_set(x_81, 1, x_47);
x_10 = x_81;
x_11 = x_78;
goto block_15;
}
else
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
lean_dec(x_80);
x_83 = l_Array_isEmpty___redArg(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_84 = lean_box(0);
x_85 = l_Lean_Expr_sort___override(x_84);
x_86 = l_Lean_Expr_getAppNumArgs(x_29);
lean_inc(x_86);
x_87 = lean_mk_array(x_86, x_85);
x_88 = lean_nat_sub(x_86, x_25);
lean_dec(x_86);
x_89 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_29, x_87, x_88);
x_90 = lean_array_get_size(x_89);
x_91 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_91, 0, x_24);
lean_ctor_set(x_91, 1, x_90);
lean_ctor_set(x_91, 2, x_25);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_26);
lean_ctor_set(x_92, 1, x_47);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_93 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg(x_82, x_89, x_1, x_50, x_91, x_92, x_24, x_5, x_6, x_7, x_8, x_78);
lean_dec(x_91);
lean_dec(x_89);
lean_dec(x_82);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_10 = x_94;
x_11 = x_95;
goto block_15;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_93;
}
}
else
{
lean_object* x_96; 
lean_dec(x_82);
lean_dec(x_29);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_26);
lean_ctor_set(x_96, 1, x_47);
x_10 = x_96;
x_11 = x_78;
goto block_15;
}
}
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_47);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_97 = !lean_is_exclusive(x_52);
if (x_97 == 0)
{
return x_52;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_52, 0);
x_99 = lean_ctor_get(x_52, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_52);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_101 = !lean_is_exclusive(x_37);
if (x_101 == 0)
{
return x_37;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_37, 0);
x_103 = lean_ctor_get(x_37, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_37);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_105 = !lean_is_exclusive(x_32);
if (x_105 == 0)
{
return x_32;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_32, 0);
x_107 = lean_ctor_get(x_32, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_32);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
block_117:
{
lean_object* x_111; 
x_111 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(x_1, x_110);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_112; uint8_t x_113; 
lean_dec(x_27);
x_112 = lean_box(0);
x_113 = lean_unbox(x_112);
x_29 = x_110;
x_30 = x_111;
x_31 = x_113;
goto block_109;
}
else
{
lean_object* x_114; 
x_114 = lean_find_expr(x_27, x_110);
lean_dec(x_27);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_box(0);
x_116 = lean_unbox(x_115);
x_29 = x_110;
x_30 = x_111;
x_31 = x_116;
goto block_109;
}
else
{
lean_dec(x_114);
x_29 = x_110;
x_30 = x_111;
x_31 = x_17;
goto block_109;
}
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_119 = !lean_is_exclusive(x_20);
if (x_119 == 0)
{
return x_20;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_20, 0);
x_121 = lean_ctor_get(x_20, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_20);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
block_15:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 2);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_3 = x_10;
x_4 = x_13;
x_9 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3_spec__3___redArg(x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_2, 1);
x_17 = lean_nat_dec_lt(x_4, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_fget(x_1, x_4);
lean_inc(x_5);
x_20 = l_Lean_Meta_getFVarLocalDecl___redArg(x_19, x_5, x_7, x_8, x_9);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_110; lean_object* x_118; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3_spec__3___redArg___lam__0___boxed), 7, 0);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_ctor_get(x_3, 0);
lean_inc(x_26);
lean_inc(x_26);
x_27 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3_spec__3___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_27, 0, x_26);
x_28 = lean_ctor_get(x_3, 1);
lean_inc(x_28);
lean_dec(x_3);
x_118 = lean_ctor_get(x_21, 3);
lean_inc(x_118);
x_110 = x_118;
goto block_117;
block_109:
{
lean_object* x_32; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_30);
x_32 = l_Lean_Meta_isProp(x_30, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_box(0);
x_36 = lean_unbox(x_35);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_30);
x_37 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1(lean_box(0), x_30, x_23, x_36, x_5, x_6, x_7, x_8, x_34);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(x_28, x_29);
lean_dec(x_28);
x_41 = l_Lean_LocalDecl_binderInfo(x_21);
lean_dec(x_21);
x_42 = lean_alloc_ctor(0, 1, 6);
lean_ctor_set(x_42, 0, x_29);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_41);
x_43 = lean_unbox(x_35);
lean_ctor_set_uint8(x_42, sizeof(void*)*1 + 1, x_43);
x_44 = lean_unbox(x_33);
lean_dec(x_33);
lean_ctor_set_uint8(x_42, sizeof(void*)*1 + 2, x_44);
x_45 = lean_unbox(x_38);
lean_dec(x_38);
lean_ctor_set_uint8(x_42, sizeof(void*)*1 + 3, x_45);
x_46 = lean_unbox(x_35);
lean_ctor_set_uint8(x_42, sizeof(void*)*1 + 4, x_46);
lean_ctor_set_uint8(x_42, sizeof(void*)*1 + 5, x_31);
x_47 = lean_array_push(x_40, x_42);
x_48 = lean_box(3);
x_49 = lean_unbox(x_48);
x_50 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_41, x_49);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_30);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_26);
lean_ctor_set(x_51, 1, x_47);
x_10 = x_51;
x_11 = x_39;
goto block_15;
}
else
{
lean_object* x_52; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_30);
x_52 = l_Lean_Meta_isClass_x3f(x_30, x_5, x_6, x_7, x_8, x_39);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_30);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_26);
lean_ctor_set(x_55, 1, x_47);
x_10 = x_55;
x_11 = x_54;
goto block_15;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_56 = lean_ctor_get(x_52, 1);
lean_inc(x_56);
lean_dec(x_52);
x_57 = lean_ctor_get(x_53, 0);
lean_inc(x_57);
lean_dec(x_53);
x_58 = lean_st_ref_get(x_8, x_56);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_ctor_get(x_58, 1);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_getOutParamPositions_x3f(x_62, x_57);
lean_dec(x_57);
if (lean_obj_tag(x_63) == 0)
{
lean_dec(x_30);
lean_ctor_set(x_58, 1, x_47);
lean_ctor_set(x_58, 0, x_26);
x_10 = x_58;
x_11 = x_61;
goto block_15;
}
else
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec(x_63);
x_65 = l_Array_isEmpty___redArg(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_66 = lean_box(0);
x_67 = l_Lean_Expr_sort___override(x_66);
x_68 = l_Lean_Expr_getAppNumArgs(x_30);
lean_inc(x_68);
x_69 = lean_mk_array(x_68, x_67);
x_70 = lean_nat_sub(x_68, x_25);
lean_dec(x_68);
x_71 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_30, x_69, x_70);
x_72 = lean_array_get_size(x_71);
x_73 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_73, 0, x_24);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_73, 2, x_25);
lean_ctor_set(x_58, 1, x_47);
lean_ctor_set(x_58, 0, x_26);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_74 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg(x_64, x_71, x_1, x_50, x_73, x_58, x_24, x_5, x_6, x_7, x_8, x_61);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_64);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_10 = x_75;
x_11 = x_76;
goto block_15;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_74;
}
}
else
{
lean_dec(x_64);
lean_dec(x_30);
lean_ctor_set(x_58, 1, x_47);
lean_ctor_set(x_58, 0, x_26);
x_10 = x_58;
x_11 = x_61;
goto block_15;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_58, 0);
x_78 = lean_ctor_get(x_58, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_58);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_getOutParamPositions_x3f(x_79, x_57);
lean_dec(x_57);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; 
lean_dec(x_30);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_26);
lean_ctor_set(x_81, 1, x_47);
x_10 = x_81;
x_11 = x_78;
goto block_15;
}
else
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
lean_dec(x_80);
x_83 = l_Array_isEmpty___redArg(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_84 = lean_box(0);
x_85 = l_Lean_Expr_sort___override(x_84);
x_86 = l_Lean_Expr_getAppNumArgs(x_30);
lean_inc(x_86);
x_87 = lean_mk_array(x_86, x_85);
x_88 = lean_nat_sub(x_86, x_25);
lean_dec(x_86);
x_89 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_30, x_87, x_88);
x_90 = lean_array_get_size(x_89);
x_91 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_91, 0, x_24);
lean_ctor_set(x_91, 1, x_90);
lean_ctor_set(x_91, 2, x_25);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_26);
lean_ctor_set(x_92, 1, x_47);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_93 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg(x_82, x_89, x_1, x_50, x_91, x_92, x_24, x_5, x_6, x_7, x_8, x_78);
lean_dec(x_91);
lean_dec(x_89);
lean_dec(x_82);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_10 = x_94;
x_11 = x_95;
goto block_15;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_93;
}
}
else
{
lean_object* x_96; 
lean_dec(x_82);
lean_dec(x_30);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_26);
lean_ctor_set(x_96, 1, x_47);
x_10 = x_96;
x_11 = x_78;
goto block_15;
}
}
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_47);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_97 = !lean_is_exclusive(x_52);
if (x_97 == 0)
{
return x_52;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_52, 0);
x_99 = lean_ctor_get(x_52, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_52);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_101 = !lean_is_exclusive(x_37);
if (x_101 == 0)
{
return x_37;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_37, 0);
x_103 = lean_ctor_get(x_37, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_37);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_105 = !lean_is_exclusive(x_32);
if (x_105 == 0)
{
return x_32;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_32, 0);
x_107 = lean_ctor_get(x_32, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_32);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
block_117:
{
lean_object* x_111; 
x_111 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(x_1, x_110);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_112; uint8_t x_113; 
lean_dec(x_27);
x_112 = lean_box(0);
x_113 = lean_unbox(x_112);
x_29 = x_111;
x_30 = x_110;
x_31 = x_113;
goto block_109;
}
else
{
lean_object* x_114; 
x_114 = lean_find_expr(x_27, x_110);
lean_dec(x_27);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_box(0);
x_116 = lean_unbox(x_115);
x_29 = x_111;
x_30 = x_110;
x_31 = x_116;
goto block_109;
}
else
{
lean_dec(x_114);
x_29 = x_111;
x_30 = x_110;
x_31 = x_17;
goto block_109;
}
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_119 = !lean_is_exclusive(x_20);
if (x_119 == 0)
{
return x_20;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_20, 0);
x_121 = lean_ctor_get(x_20, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_20);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
block_15:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_2, 2);
x_13 = lean_nat_add(x_4, x_12);
x_14 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3_spec__3___redArg(x_1, x_2, x_10, x_13, x_5, x_6, x_7, x_8, x_11);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___redArg(x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5_spec__5_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_1324_(x_4, x_8);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5_spec__5_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5_spec__5_spec__5___redArg(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5_spec__5___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
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
x_18 = l___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_1324_(x_3, x_16);
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
x_37 = l___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_1324_(x_3, x_35);
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
x_47 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5_spec__5_spec__5___redArg(x_44, x_45, x_46, x_3);
lean_dec(x_45);
lean_dec(x_44);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5_spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5_spec__5___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; lean_object* x_5; uint64_t x_6; uint64_t x_7; 
x_3 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = l_Lean_Expr_hash(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_13; uint64_t x_14; 
x_13 = lean_unsigned_to_nat(11u);
x_14 = lean_uint64_of_nat(x_13);
x_7 = x_14;
goto block_12;
}
else
{
lean_object* x_15; uint64_t x_16; lean_object* x_17; uint64_t x_18; uint64_t x_19; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_uint64_of_nat(x_15);
x_17 = lean_unsigned_to_nat(13u);
x_18 = lean_uint64_of_nat(x_17);
x_19 = lean_uint64_mix_hash(x_16, x_18);
x_7 = x_19;
goto block_12;
}
block_12:
{
uint64_t x_8; uint64_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_uint64_mix_hash(x_6, x_7);
x_9 = lean_uint64_mix_hash(x_3, x_8);
x_10 = lean_uint64_to_usize(x_9);
x_11 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5_spec__5___redArg(x_1, x_10, x_2);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; 
x_4 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = l_Lean_Meta_instBEqInfoCacheKey;
x_8 = l_Lean_Meta_instHashableInfoCacheKey;
x_9 = l_Lean_Expr_hash(x_5);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_18; uint64_t x_19; 
x_18 = lean_unsigned_to_nat(11u);
x_19 = lean_uint64_of_nat(x_18);
x_10 = x_19;
goto block_17;
}
else
{
lean_object* x_20; uint64_t x_21; lean_object* x_22; uint64_t x_23; uint64_t x_24; 
x_20 = lean_ctor_get(x_6, 0);
lean_inc(x_20);
lean_dec(x_6);
x_21 = lean_uint64_of_nat(x_20);
lean_dec(x_20);
x_22 = lean_unsigned_to_nat(13u);
x_23 = lean_uint64_of_nat(x_22);
x_24 = lean_uint64_mix_hash(x_21, x_23);
x_10 = x_24;
goto block_17;
}
block_17:
{
uint64_t x_11; uint64_t x_12; size_t x_13; lean_object* x_14; size_t x_15; lean_object* x_16; 
x_11 = lean_uint64_mix_hash(x_9, x_10);
x_12 = lean_uint64_mix_hash(x_4, x_11);
x_13 = lean_uint64_to_usize(x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert_spec__0___redArg(x_7, x_8, x_1, x_13, x_15, x_2, x_3);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_mk_empty_array_with_capacity(x_8);
x_10 = lean_box(0);
x_11 = lean_array_get_size(x_1);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_9);
x_15 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___redArg(x_1, x_13, x_14, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_13);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_17, 1);
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(x_1, x_2);
x_22 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(x_19, x_21);
lean_dec(x_19);
lean_ctor_set(x_17, 1, x_21);
lean_ctor_set(x_17, 0, x_22);
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(x_1, x_2);
x_25 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(x_23, x_24);
lean_dec(x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_15, 0, x_26);
return x_15;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_ctor_get(x_15, 0);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_15);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
x_31 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(x_1, x_2);
x_32 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(x_29, x_31);
lean_dec(x_29);
if (lean_is_scalar(x_30)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_30;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_28);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_15);
if (x_35 == 0)
{
return x_15;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_15, 0);
x_37 = lean_ctor_get(x_15, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_15);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_Lean_Meta_mkInfoCacheKey___redArg(x_1, x_2, x_3, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_get(x_4, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(x_16, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_free_object(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_18 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_closure((void*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0___boxed), 7, 0);
x_22 = lean_box(1);
x_23 = lean_box(0);
x_88 = lean_ctor_get(x_3, 0);
lean_inc(x_88);
x_89 = lean_ctor_get_uint8(x_88, 9);
lean_dec(x_88);
x_90 = lean_unbox(x_22);
x_91 = l_Lean_Meta_TransparencyMode_lt(x_89, x_90);
if (x_91 == 0)
{
x_24 = x_89;
goto block_87;
}
else
{
uint8_t x_92; 
x_92 = lean_unbox(x_22);
x_24 = x_92;
goto block_87;
}
block_87:
{
lean_object* x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; uint64_t x_44; lean_object* x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; 
x_25 = lean_ctor_get(x_3, 0);
lean_inc(x_25);
x_26 = lean_ctor_get_uint8(x_25, 0);
x_27 = lean_ctor_get_uint8(x_25, 1);
x_28 = lean_ctor_get_uint8(x_25, 2);
x_29 = lean_ctor_get_uint8(x_25, 3);
x_30 = lean_ctor_get_uint8(x_25, 4);
x_31 = lean_ctor_get_uint8(x_25, 5);
x_32 = lean_ctor_get_uint8(x_25, 6);
x_33 = lean_ctor_get_uint8(x_25, 7);
x_34 = lean_ctor_get_uint8(x_25, 8);
x_35 = lean_ctor_get_uint8(x_25, 10);
x_36 = lean_ctor_get_uint8(x_25, 11);
x_37 = lean_ctor_get_uint8(x_25, 12);
x_38 = lean_ctor_get_uint8(x_25, 13);
x_39 = lean_ctor_get_uint8(x_25, 14);
x_40 = lean_ctor_get_uint8(x_25, 15);
x_41 = lean_ctor_get_uint8(x_25, 16);
x_42 = lean_ctor_get_uint8(x_25, 17);
lean_dec(x_25);
x_43 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_43, 0, x_26);
lean_ctor_set_uint8(x_43, 1, x_27);
lean_ctor_set_uint8(x_43, 2, x_28);
lean_ctor_set_uint8(x_43, 3, x_29);
lean_ctor_set_uint8(x_43, 4, x_30);
lean_ctor_set_uint8(x_43, 5, x_31);
lean_ctor_set_uint8(x_43, 6, x_32);
lean_ctor_set_uint8(x_43, 7, x_33);
lean_ctor_set_uint8(x_43, 8, x_34);
lean_ctor_set_uint8(x_43, 9, x_24);
lean_ctor_set_uint8(x_43, 10, x_35);
lean_ctor_set_uint8(x_43, 11, x_36);
lean_ctor_set_uint8(x_43, 12, x_37);
lean_ctor_set_uint8(x_43, 13, x_38);
lean_ctor_set_uint8(x_43, 14, x_39);
lean_ctor_set_uint8(x_43, 15, x_40);
lean_ctor_set_uint8(x_43, 16, x_41);
lean_ctor_set_uint8(x_43, 17, x_42);
x_44 = lean_ctor_get_uint64(x_3, sizeof(void*)*7);
x_45 = lean_unsigned_to_nat(2u);
x_46 = lean_uint64_of_nat(x_45);
x_47 = lean_uint64_shift_right(x_44, x_46);
x_48 = lean_uint64_shift_left(x_47, x_46);
x_49 = l_Lean_Meta_TransparencyMode_toUInt64(x_24);
x_50 = lean_uint64_lor(x_48, x_49);
x_51 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 8);
x_52 = lean_ctor_get(x_3, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_3, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_3, 3);
lean_inc(x_54);
x_55 = lean_ctor_get(x_3, 4);
lean_inc(x_55);
x_56 = lean_ctor_get(x_3, 5);
lean_inc(x_56);
x_57 = lean_ctor_get(x_3, 6);
lean_inc(x_57);
x_58 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 9);
x_59 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 10);
lean_dec(x_3);
x_60 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_60, 0, x_43);
lean_ctor_set(x_60, 1, x_52);
lean_ctor_set(x_60, 2, x_53);
lean_ctor_set(x_60, 3, x_54);
lean_ctor_set(x_60, 4, x_55);
lean_ctor_set(x_60, 5, x_56);
lean_ctor_set(x_60, 6, x_57);
lean_ctor_set_uint64(x_60, sizeof(void*)*7, x_50);
lean_ctor_set_uint8(x_60, sizeof(void*)*7 + 8, x_51);
lean_ctor_set_uint8(x_60, sizeof(void*)*7 + 9, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*7 + 10, x_59);
x_61 = lean_unbox(x_23);
lean_inc(x_4);
x_62 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6(lean_box(0), x_19, x_2, x_21, x_61, x_60, x_4, x_5, x_6, x_20);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_st_ref_take(x_4, x_64);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_inc(x_63);
x_72 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg(x_71, x_9, x_63);
x_73 = lean_ctor_get(x_69, 2);
lean_inc(x_73);
x_74 = lean_ctor_get(x_69, 3);
lean_inc(x_74);
x_75 = lean_ctor_get(x_69, 4);
lean_inc(x_75);
x_76 = lean_ctor_get(x_69, 5);
lean_inc(x_76);
lean_dec(x_69);
x_77 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_77, 0, x_70);
lean_ctor_set(x_77, 1, x_72);
lean_ctor_set(x_77, 2, x_73);
lean_ctor_set(x_77, 3, x_74);
lean_ctor_set(x_77, 4, x_75);
lean_ctor_set(x_77, 5, x_76);
x_78 = lean_ctor_get(x_66, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_66, 3);
lean_inc(x_79);
x_80 = lean_ctor_get(x_66, 4);
lean_inc(x_80);
lean_dec(x_66);
x_81 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_81, 0, x_68);
lean_ctor_set(x_81, 1, x_77);
lean_ctor_set(x_81, 2, x_78);
lean_ctor_set(x_81, 3, x_79);
lean_ctor_set(x_81, 4, x_80);
x_82 = lean_st_ref_set(x_4, x_81, x_67);
lean_dec(x_4);
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_82, 0);
lean_dec(x_84);
lean_ctor_set(x_82, 0, x_63);
return x_82;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_63);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
else
{
lean_dec(x_9);
lean_dec(x_4);
return x_62;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_93 = !lean_is_exclusive(x_18);
if (x_93 == 0)
{
return x_18;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_18, 0);
x_95 = lean_ctor_get(x_18, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_18);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
else
{
lean_object* x_97; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_97 = lean_ctor_get(x_17, 0);
lean_inc(x_97);
lean_dec(x_17);
lean_ctor_set(x_11, 0, x_97);
return x_11;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_11, 0);
x_99 = lean_ctor_get(x_11, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_11);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
x_102 = l_Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(x_101, x_9);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_103 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_99);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_172; uint8_t x_173; uint8_t x_174; uint8_t x_175; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_alloc_closure((void*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0___boxed), 7, 0);
x_107 = lean_box(1);
x_108 = lean_box(0);
x_172 = lean_ctor_get(x_3, 0);
lean_inc(x_172);
x_173 = lean_ctor_get_uint8(x_172, 9);
lean_dec(x_172);
x_174 = lean_unbox(x_107);
x_175 = l_Lean_Meta_TransparencyMode_lt(x_173, x_174);
if (x_175 == 0)
{
x_109 = x_173;
goto block_171;
}
else
{
uint8_t x_176; 
x_176 = lean_unbox(x_107);
x_109 = x_176;
goto block_171;
}
block_171:
{
lean_object* x_110; uint8_t x_111; uint8_t x_112; uint8_t x_113; uint8_t x_114; uint8_t x_115; uint8_t x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; lean_object* x_128; uint64_t x_129; lean_object* x_130; uint64_t x_131; uint64_t x_132; uint64_t x_133; uint64_t x_134; uint64_t x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; uint8_t x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; 
x_110 = lean_ctor_get(x_3, 0);
lean_inc(x_110);
x_111 = lean_ctor_get_uint8(x_110, 0);
x_112 = lean_ctor_get_uint8(x_110, 1);
x_113 = lean_ctor_get_uint8(x_110, 2);
x_114 = lean_ctor_get_uint8(x_110, 3);
x_115 = lean_ctor_get_uint8(x_110, 4);
x_116 = lean_ctor_get_uint8(x_110, 5);
x_117 = lean_ctor_get_uint8(x_110, 6);
x_118 = lean_ctor_get_uint8(x_110, 7);
x_119 = lean_ctor_get_uint8(x_110, 8);
x_120 = lean_ctor_get_uint8(x_110, 10);
x_121 = lean_ctor_get_uint8(x_110, 11);
x_122 = lean_ctor_get_uint8(x_110, 12);
x_123 = lean_ctor_get_uint8(x_110, 13);
x_124 = lean_ctor_get_uint8(x_110, 14);
x_125 = lean_ctor_get_uint8(x_110, 15);
x_126 = lean_ctor_get_uint8(x_110, 16);
x_127 = lean_ctor_get_uint8(x_110, 17);
lean_dec(x_110);
x_128 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_128, 0, x_111);
lean_ctor_set_uint8(x_128, 1, x_112);
lean_ctor_set_uint8(x_128, 2, x_113);
lean_ctor_set_uint8(x_128, 3, x_114);
lean_ctor_set_uint8(x_128, 4, x_115);
lean_ctor_set_uint8(x_128, 5, x_116);
lean_ctor_set_uint8(x_128, 6, x_117);
lean_ctor_set_uint8(x_128, 7, x_118);
lean_ctor_set_uint8(x_128, 8, x_119);
lean_ctor_set_uint8(x_128, 9, x_109);
lean_ctor_set_uint8(x_128, 10, x_120);
lean_ctor_set_uint8(x_128, 11, x_121);
lean_ctor_set_uint8(x_128, 12, x_122);
lean_ctor_set_uint8(x_128, 13, x_123);
lean_ctor_set_uint8(x_128, 14, x_124);
lean_ctor_set_uint8(x_128, 15, x_125);
lean_ctor_set_uint8(x_128, 16, x_126);
lean_ctor_set_uint8(x_128, 17, x_127);
x_129 = lean_ctor_get_uint64(x_3, sizeof(void*)*7);
x_130 = lean_unsigned_to_nat(2u);
x_131 = lean_uint64_of_nat(x_130);
x_132 = lean_uint64_shift_right(x_129, x_131);
x_133 = lean_uint64_shift_left(x_132, x_131);
x_134 = l_Lean_Meta_TransparencyMode_toUInt64(x_109);
x_135 = lean_uint64_lor(x_133, x_134);
x_136 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 8);
x_137 = lean_ctor_get(x_3, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_3, 2);
lean_inc(x_138);
x_139 = lean_ctor_get(x_3, 3);
lean_inc(x_139);
x_140 = lean_ctor_get(x_3, 4);
lean_inc(x_140);
x_141 = lean_ctor_get(x_3, 5);
lean_inc(x_141);
x_142 = lean_ctor_get(x_3, 6);
lean_inc(x_142);
x_143 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 9);
x_144 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 10);
lean_dec(x_3);
x_145 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_145, 0, x_128);
lean_ctor_set(x_145, 1, x_137);
lean_ctor_set(x_145, 2, x_138);
lean_ctor_set(x_145, 3, x_139);
lean_ctor_set(x_145, 4, x_140);
lean_ctor_set(x_145, 5, x_141);
lean_ctor_set(x_145, 6, x_142);
lean_ctor_set_uint64(x_145, sizeof(void*)*7, x_135);
lean_ctor_set_uint8(x_145, sizeof(void*)*7 + 8, x_136);
lean_ctor_set_uint8(x_145, sizeof(void*)*7 + 9, x_143);
lean_ctor_set_uint8(x_145, sizeof(void*)*7 + 10, x_144);
x_146 = lean_unbox(x_108);
lean_inc(x_4);
x_147 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6(lean_box(0), x_104, x_2, x_106, x_146, x_145, x_4, x_5, x_6, x_105);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = lean_st_ref_take(x_4, x_149);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = lean_ctor_get(x_151, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_151, 1);
lean_inc(x_154);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_inc(x_148);
x_157 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__8___redArg(x_156, x_9, x_148);
x_158 = lean_ctor_get(x_154, 2);
lean_inc(x_158);
x_159 = lean_ctor_get(x_154, 3);
lean_inc(x_159);
x_160 = lean_ctor_get(x_154, 4);
lean_inc(x_160);
x_161 = lean_ctor_get(x_154, 5);
lean_inc(x_161);
lean_dec(x_154);
x_162 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_162, 0, x_155);
lean_ctor_set(x_162, 1, x_157);
lean_ctor_set(x_162, 2, x_158);
lean_ctor_set(x_162, 3, x_159);
lean_ctor_set(x_162, 4, x_160);
lean_ctor_set(x_162, 5, x_161);
x_163 = lean_ctor_get(x_151, 2);
lean_inc(x_163);
x_164 = lean_ctor_get(x_151, 3);
lean_inc(x_164);
x_165 = lean_ctor_get(x_151, 4);
lean_inc(x_165);
lean_dec(x_151);
x_166 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_166, 0, x_153);
lean_ctor_set(x_166, 1, x_162);
lean_ctor_set(x_166, 2, x_163);
lean_ctor_set(x_166, 3, x_164);
lean_ctor_set(x_166, 4, x_165);
x_167 = lean_st_ref_set(x_4, x_166, x_152);
lean_dec(x_4);
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_169 = x_167;
} else {
 lean_dec_ref(x_167);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_148);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
else
{
lean_dec(x_9);
lean_dec(x_4);
return x_147;
}
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_177 = lean_ctor_get(x_103, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_103, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_179 = x_103;
} else {
 lean_dec_ref(x_103);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(1, 2, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
}
else
{
lean_object* x_181; lean_object* x_182; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_181 = lean_ctor_get(x_102, 0);
lean_inc(x_181);
lean_dec(x_102);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_99);
return x_182;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1_spec__1___redArg(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1_spec__1(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___redArg(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__1(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3_spec__3___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3_spec__3___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3_spec__3___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3_spec__3___redArg___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5_spec__5_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5_spec__5_spec__5___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5_spec__5_spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5_spec__5___redArg(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5_spec__5(x_1, x_2, x_5, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__5(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_2);
x_9 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInfo_getArity(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_array_get_size(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInfo_getArity___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_FunInfo_getArity(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_InferType(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_FunInfo(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_InferType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
