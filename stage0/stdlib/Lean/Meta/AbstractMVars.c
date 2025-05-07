// Lean compiler output
// Module: Lean.Meta.AbstractMVars
// Imports: Lean.Meta.Basic
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
uint8_t l_ptrEqList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
lean_object* l_StateT_get(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__7(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelMax_x27(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__3_spec__3_spec__3___redArg(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaMetaTelescope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_openAbstractMVarsResult_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___lam__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractMVars___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg___boxed(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_MetavarContext_getLevelDepth(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__3(lean_object*, lean_object*);
lean_object* l_panic___at___Lean_Expr_appFn_x21_spec__0(lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractMVars(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__1___redArg___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
uint64_t l___private_Lean_Level_0__Lean_hashLevelMVarId____x40_Lean_Level___hyg_522_(lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_instantiateLevelParamsArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractMVars___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_simpLevelIMax_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Expr_0__Lean_hashMVarId____x40_Lean_Expr___hyg_1984_(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_mkFreshFVarId(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__3_spec__3_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLambda(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_openAbstractMVarsResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2_spec__2_spec__2___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__3___redArg(lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_simpLevelMax_x27(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_openAbstractMVarsResult_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_mkFreshId(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_openAbstractMVarsResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_abstractExprMVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__5___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__1___redArg(lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_3 = lean_box(0);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_apply_1(x_1, x_6);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 4);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 5);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 6);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 7);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_2, sizeof(void*)*8);
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 2, x_7);
lean_ctor_set(x_14, 3, x_8);
lean_ctor_set(x_14, 4, x_9);
lean_ctor_set(x_14, 5, x_10);
lean_ctor_set(x_14, 6, x_11);
lean_ctor_set(x_14, 7, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*8, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
static lean_object* _init_l_Lean_Meta_AbstractMVars_instMonadMCtxM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_AbstractMVars_instMonadMCtxM___lam__0___boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_AbstractMVars_instMonadMCtxM___lam__1), 2, 0);
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
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_AbstractMVars_instMonadMCtxM___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_mkFreshId(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
lean_inc(x_4);
lean_inc(x_3);
x_5 = l_Lean_Name_num___override(x_3, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 4);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 5);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 6);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 7);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_9);
lean_ctor_set(x_17, 2, x_10);
lean_ctor_set(x_17, 3, x_11);
lean_ctor_set(x_17, 4, x_12);
lean_ctor_set(x_17, 5, x_13);
lean_ctor_set(x_17, 6, x_14);
lean_ctor_set(x_17, 7, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*8, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_mkFreshFVarId(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Meta_AbstractMVars_mkFreshId(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_name_eq(x_4, x_1);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_name_eq(x_5, x_1);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = l___private_Lean_Level_0__Lean_hashLevelMVarId____x40_Lean_Level___hyg_522_(x_4);
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
x_29 = l___private_Lean_Level_0__Lean_hashLevelMVarId____x40_Lean_Level___hyg_522_(x_25);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2_spec__2_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2_spec__2_spec__2___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2___redArg(lean_object* x_1) {
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
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2_spec__2___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = lean_name_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__5___redArg(x_1, x_2, x_7);
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
x_13 = lean_name_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__5___redArg(x_1, x_2, x_12);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__5___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_2, sizeof(void*)*8);
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
uint8_t x_5; 
x_5 = l_Lean_Level_hasMVar(x_1);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
else
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_inc(x_7);
x_8 = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(x_7, x_2);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; size_t x_11; size_t x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ptr_addr(x_7);
lean_dec(x_7);
x_12 = lean_ptr_addr(x_10);
x_13 = lean_usize_dec_eq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_1);
x_14 = l_Lean_Level_succ___override(x_10);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
lean_dec(x_10);
lean_ctor_set(x_8, 0, x_1);
return x_8;
}
}
else
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_17 = lean_ptr_addr(x_7);
lean_dec(x_7);
x_18 = lean_ptr_addr(x_15);
x_19 = lean_usize_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_20 = l_Lean_Level_succ___override(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_15);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_16);
return x_22;
}
}
}
case 2:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; size_t x_38; size_t x_39; uint8_t x_40; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_inc(x_23);
x_25 = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(x_23, x_2);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_24);
x_28 = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(x_24, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_31 = x_28;
} else {
 lean_dec_ref(x_28);
 x_31 = lean_box(0);
}
x_38 = lean_ptr_addr(x_23);
lean_dec(x_23);
x_39 = lean_ptr_addr(x_26);
x_40 = lean_usize_dec_eq(x_38, x_39);
if (x_40 == 0)
{
lean_dec(x_24);
x_32 = x_40;
goto block_37;
}
else
{
size_t x_41; size_t x_42; uint8_t x_43; 
x_41 = lean_ptr_addr(x_24);
lean_dec(x_24);
x_42 = lean_ptr_addr(x_29);
x_43 = lean_usize_dec_eq(x_41, x_42);
x_32 = x_43;
goto block_37;
}
block_37:
{
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_1);
x_33 = l_Lean_mkLevelMax_x27(x_26, x_29);
if (lean_is_scalar(x_31)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_31;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_30);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_Lean_simpLevelMax_x27(x_26, x_29, x_1);
lean_dec(x_1);
lean_dec(x_29);
lean_dec(x_26);
if (lean_is_scalar(x_31)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_31;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_30);
return x_36;
}
}
}
case 3:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; size_t x_59; size_t x_60; uint8_t x_61; 
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
lean_inc(x_44);
x_46 = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(x_44, x_2);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_45);
x_49 = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(x_45, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_52 = x_49;
} else {
 lean_dec_ref(x_49);
 x_52 = lean_box(0);
}
x_59 = lean_ptr_addr(x_44);
lean_dec(x_44);
x_60 = lean_ptr_addr(x_47);
x_61 = lean_usize_dec_eq(x_59, x_60);
if (x_61 == 0)
{
lean_dec(x_45);
x_53 = x_61;
goto block_58;
}
else
{
size_t x_62; size_t x_63; uint8_t x_64; 
x_62 = lean_ptr_addr(x_45);
lean_dec(x_45);
x_63 = lean_ptr_addr(x_50);
x_64 = lean_usize_dec_eq(x_62, x_63);
x_53 = x_64;
goto block_58;
}
block_58:
{
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_1);
x_54 = l_Lean_mkLevelIMax_x27(x_47, x_50);
if (lean_is_scalar(x_52)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_52;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_51);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = l_Lean_simpLevelIMax_x27(x_47, x_50, x_1);
lean_dec(x_1);
if (lean_is_scalar(x_52)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_52;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_51);
return x_57;
}
}
}
case 5:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_65 = lean_ctor_get(x_1, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_2, 2);
lean_inc(x_66);
lean_inc(x_66);
x_67 = l_Lean_MetavarContext_getLevelDepth(x_66, x_65);
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
x_69 = lean_nat_dec_eq(x_67, x_68);
lean_dec(x_68);
lean_dec(x_67);
if (x_69 == 0)
{
lean_object* x_70; 
lean_dec(x_66);
lean_dec(x_65);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_1);
lean_ctor_set(x_70, 1, x_2);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint64_t x_74; lean_object* x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; lean_object* x_79; uint64_t x_80; uint64_t x_81; uint64_t x_82; size_t x_83; size_t x_84; lean_object* x_85; size_t x_86; size_t x_87; size_t x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_1);
x_71 = lean_ctor_get(x_2, 6);
lean_inc(x_71);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
x_73 = lean_array_get_size(x_72);
x_74 = l___private_Lean_Level_0__Lean_hashLevelMVarId____x40_Lean_Level___hyg_522_(x_65);
x_75 = lean_unsigned_to_nat(32u);
x_76 = lean_uint64_of_nat(x_75);
x_77 = lean_uint64_shift_right(x_74, x_76);
x_78 = lean_uint64_xor(x_74, x_77);
x_79 = lean_unsigned_to_nat(16u);
x_80 = lean_uint64_of_nat(x_79);
x_81 = lean_uint64_shift_right(x_78, x_80);
x_82 = lean_uint64_xor(x_78, x_81);
x_83 = lean_uint64_to_usize(x_82);
x_84 = lean_usize_of_nat(x_73);
lean_dec(x_73);
x_85 = lean_unsigned_to_nat(1u);
x_86 = lean_usize_of_nat(x_85);
x_87 = lean_usize_sub(x_84, x_86);
x_88 = lean_usize_land(x_83, x_87);
x_89 = lean_array_uget(x_72, x_88);
lean_dec(x_72);
x_90 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(x_65, x_89);
lean_dec(x_89);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_mk_string_unchecked("_abstMVar", 9, 9);
x_92 = !lean_is_exclusive(x_71);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_110; size_t x_111; size_t x_112; size_t x_113; lean_object* x_114; uint8_t x_115; 
x_93 = lean_ctor_get(x_71, 0);
x_94 = lean_ctor_get(x_71, 1);
x_95 = l_Lean_Name_mkStr1(x_91);
x_96 = lean_ctor_get(x_2, 3);
lean_inc(x_96);
x_97 = lean_ctor_get(x_2, 4);
lean_inc(x_97);
lean_inc(x_96);
x_98 = l_Lean_Name_num___override(x_95, x_96);
x_99 = lean_ctor_get(x_2, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_2, 1);
lean_inc(x_100);
x_101 = lean_nat_add(x_96, x_85);
lean_dec(x_96);
lean_inc(x_98);
x_102 = lean_array_push(x_97, x_98);
x_103 = lean_ctor_get(x_2, 5);
lean_inc(x_103);
x_104 = l_Lean_Level_param___override(x_98);
x_110 = lean_array_get_size(x_94);
x_111 = lean_usize_of_nat(x_110);
lean_dec(x_110);
x_112 = lean_usize_sub(x_111, x_86);
x_113 = lean_usize_land(x_83, x_112);
x_114 = lean_array_uget(x_94, x_113);
x_115 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(x_65, x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_116 = lean_nat_add(x_93, x_85);
lean_dec(x_93);
lean_inc(x_104);
x_117 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_117, 0, x_65);
lean_ctor_set(x_117, 1, x_104);
lean_ctor_set(x_117, 2, x_114);
x_118 = lean_array_uset(x_94, x_113, x_117);
x_119 = lean_unsigned_to_nat(2u);
x_120 = lean_nat_shiftl(x_116, x_119);
x_121 = lean_unsigned_to_nat(3u);
x_122 = lean_nat_div(x_120, x_121);
lean_dec(x_120);
x_123 = lean_array_get_size(x_118);
x_124 = lean_nat_dec_le(x_122, x_123);
lean_dec(x_123);
lean_dec(x_122);
if (x_124 == 0)
{
lean_object* x_125; 
x_125 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2___redArg(x_118);
lean_ctor_set(x_71, 1, x_125);
lean_ctor_set(x_71, 0, x_116);
x_105 = x_71;
goto block_109;
}
else
{
lean_ctor_set(x_71, 1, x_118);
lean_ctor_set(x_71, 0, x_116);
x_105 = x_71;
goto block_109;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_126 = lean_box(0);
x_127 = lean_array_uset(x_94, x_113, x_126);
lean_inc(x_104);
x_128 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__5___redArg(x_65, x_104, x_114);
x_129 = lean_array_uset(x_127, x_113, x_128);
lean_ctor_set(x_71, 1, x_129);
x_105 = x_71;
goto block_109;
}
block_109:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_2, 7);
lean_inc(x_106);
lean_dec(x_2);
x_107 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_107, 0, x_99);
lean_ctor_set(x_107, 1, x_100);
lean_ctor_set(x_107, 2, x_66);
lean_ctor_set(x_107, 3, x_101);
lean_ctor_set(x_107, 4, x_102);
lean_ctor_set(x_107, 5, x_103);
lean_ctor_set(x_107, 6, x_105);
lean_ctor_set(x_107, 7, x_106);
lean_ctor_set_uint8(x_107, sizeof(void*)*8, x_3);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_104);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_147; size_t x_148; size_t x_149; size_t x_150; lean_object* x_151; uint8_t x_152; 
x_130 = lean_ctor_get(x_71, 0);
x_131 = lean_ctor_get(x_71, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_71);
x_132 = l_Lean_Name_mkStr1(x_91);
x_133 = lean_ctor_get(x_2, 3);
lean_inc(x_133);
x_134 = lean_ctor_get(x_2, 4);
lean_inc(x_134);
lean_inc(x_133);
x_135 = l_Lean_Name_num___override(x_132, x_133);
x_136 = lean_ctor_get(x_2, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_2, 1);
lean_inc(x_137);
x_138 = lean_nat_add(x_133, x_85);
lean_dec(x_133);
lean_inc(x_135);
x_139 = lean_array_push(x_134, x_135);
x_140 = lean_ctor_get(x_2, 5);
lean_inc(x_140);
x_141 = l_Lean_Level_param___override(x_135);
x_147 = lean_array_get_size(x_131);
x_148 = lean_usize_of_nat(x_147);
lean_dec(x_147);
x_149 = lean_usize_sub(x_148, x_86);
x_150 = lean_usize_land(x_83, x_149);
x_151 = lean_array_uget(x_131, x_150);
x_152 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(x_65, x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_153 = lean_nat_add(x_130, x_85);
lean_dec(x_130);
lean_inc(x_141);
x_154 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_154, 0, x_65);
lean_ctor_set(x_154, 1, x_141);
lean_ctor_set(x_154, 2, x_151);
x_155 = lean_array_uset(x_131, x_150, x_154);
x_156 = lean_unsigned_to_nat(2u);
x_157 = lean_nat_shiftl(x_153, x_156);
x_158 = lean_unsigned_to_nat(3u);
x_159 = lean_nat_div(x_157, x_158);
lean_dec(x_157);
x_160 = lean_array_get_size(x_155);
x_161 = lean_nat_dec_le(x_159, x_160);
lean_dec(x_160);
lean_dec(x_159);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; 
x_162 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2___redArg(x_155);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_153);
lean_ctor_set(x_163, 1, x_162);
x_142 = x_163;
goto block_146;
}
else
{
lean_object* x_164; 
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_153);
lean_ctor_set(x_164, 1, x_155);
x_142 = x_164;
goto block_146;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_165 = lean_box(0);
x_166 = lean_array_uset(x_131, x_150, x_165);
lean_inc(x_141);
x_167 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__5___redArg(x_65, x_141, x_151);
x_168 = lean_array_uset(x_166, x_150, x_167);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_130);
lean_ctor_set(x_169, 1, x_168);
x_142 = x_169;
goto block_146;
}
block_146:
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_2, 7);
lean_inc(x_143);
lean_dec(x_2);
x_144 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_144, 0, x_136);
lean_ctor_set(x_144, 1, x_137);
lean_ctor_set(x_144, 2, x_66);
lean_ctor_set(x_144, 3, x_138);
lean_ctor_set(x_144, 4, x_139);
lean_ctor_set(x_144, 5, x_140);
lean_ctor_set(x_144, 6, x_142);
lean_ctor_set(x_144, 7, x_143);
lean_ctor_set_uint8(x_144, sizeof(void*)*8, x_3);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_141);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_71);
lean_dec(x_66);
lean_dec(x_65);
x_170 = lean_ctor_get(x_90, 0);
lean_inc(x_170);
lean_dec(x_90);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_2);
return x_171;
}
}
}
default: 
{
lean_object* x_172; 
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_1);
lean_ctor_set(x_172, 1, x_2);
return x_172;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__0(lean_object* x_1, lean_object* x_2) {
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
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = l_Lean_instantiateMVarsCore(x_5, x_1);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_8 = lean_ctor_get(x_6, 1);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 4);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 5);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 6);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 7);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_2, sizeof(void*)*8);
lean_dec(x_2);
x_17 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_10);
lean_ctor_set(x_17, 2, x_8);
lean_ctor_set(x_17, 3, x_11);
lean_ctor_set(x_17, 4, x_12);
lean_ctor_set(x_17, 5, x_13);
lean_ctor_set(x_17, 6, x_14);
lean_ctor_set(x_17, 7, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*8, x_16);
lean_ctor_set(x_6, 1, x_17);
return x_6;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 3);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 4);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 5);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 6);
lean_inc(x_25);
x_26 = lean_ctor_get(x_2, 7);
lean_inc(x_26);
x_27 = lean_ctor_get_uint8(x_2, sizeof(void*)*8);
lean_dec(x_2);
x_28 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_21);
lean_ctor_set(x_28, 2, x_19);
lean_ctor_set(x_28, 3, x_22);
lean_ctor_set(x_28, 4, x_23);
lean_ctor_set(x_28, 5, x_24);
lean_ctor_set(x_28, 6, x_25);
lean_ctor_set(x_28, 7, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*8, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_18);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_name_eq(x_4, x_1);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_name_eq(x_5, x_1);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__3_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = l___private_Lean_Expr_0__Lean_hashMVarId____x40_Lean_Expr___hyg_1984_(x_4);
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
x_29 = l___private_Lean_Expr_0__Lean_hashMVarId____x40_Lean_Expr___hyg_1984_(x_25);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__3_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__3_spec__3_spec__3___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__3_spec__3_spec__3___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__3_spec__3___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__3___redArg(lean_object* x_1) {
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
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__3_spec__3___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__3___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = lean_name_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__6___redArg(x_1, x_2, x_7);
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
x_13 = lean_name_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__6___redArg(x_1, x_2, x_12);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__6___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_List_reverse___redArg(x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(x_7, x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_10);
{
lean_object* _tmp_0 = x_8;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_2 = x_11;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(x_13, x_3);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_2);
x_1 = x_14;
x_2 = x_18;
x_3 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_abstractExprMVars(lean_object* x_1, lean_object* x_2) {
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
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_inc(x_6);
x_7 = l_Lean_MetavarContext_getDecl(x_6, x_5);
x_8 = lean_ctor_get(x_7, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_2);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
lean_inc(x_1);
x_12 = l_Lean_instantiateMVars___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__0(x_1, x_2);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_expr_eqv(x_1, x_14);
lean_dec(x_1);
if (x_16 == 0)
{
lean_free_object(x_12);
lean_dec(x_7);
lean_dec(x_5);
x_1 = x_14;
x_2 = x_15;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint64_t x_21; lean_object* x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; lean_object* x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; size_t x_30; size_t x_31; lean_object* x_32; size_t x_33; size_t x_34; size_t x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_14);
x_18 = lean_ctor_get(x_15, 7);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_array_get_size(x_19);
x_21 = l___private_Lean_Expr_0__Lean_hashMVarId____x40_Lean_Expr___hyg_1984_(x_5);
x_22 = lean_unsigned_to_nat(32u);
x_23 = lean_uint64_of_nat(x_22);
x_24 = lean_uint64_shift_right(x_21, x_23);
x_25 = lean_uint64_xor(x_21, x_24);
x_26 = lean_unsigned_to_nat(16u);
x_27 = lean_uint64_of_nat(x_26);
x_28 = lean_uint64_shift_right(x_25, x_27);
x_29 = lean_uint64_xor(x_25, x_28);
x_30 = lean_uint64_to_usize(x_29);
x_31 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_usize_of_nat(x_32);
x_34 = lean_usize_sub(x_31, x_33);
x_35 = lean_usize_land(x_30, x_34);
x_36 = lean_array_uget(x_19, x_35);
lean_dec(x_19);
x_37 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__1___redArg(x_5, x_36);
lean_dec(x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_60; lean_object* x_137; uint8_t x_138; 
lean_free_object(x_12);
x_38 = lean_ctor_get(x_7, 2);
lean_inc(x_38);
x_39 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_38, x_15);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Meta_AbstractMVars_mkFreshFVarId(x_41);
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
lean_inc(x_43);
x_46 = l_Lean_Expr_fvar___override(x_43);
x_137 = lean_ctor_get(x_7, 0);
lean_inc(x_137);
lean_dec(x_7);
x_138 = l_Lean_Name_isAnonymous(x_137);
if (x_138 == 0)
{
x_60 = x_137;
goto block_136;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_137);
x_139 = lean_mk_string_unchecked("x", 1, 1);
x_140 = l_Lean_Name_mkStr1(x_139);
x_141 = lean_ctor_get(x_44, 5);
lean_inc(x_141);
x_142 = lean_array_get_size(x_141);
lean_dec(x_141);
x_143 = lean_name_append_index_after(x_140, x_142);
x_60 = x_143;
goto block_136;
}
block_59:
{
uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get_uint8(x_50, sizeof(void*)*8);
lean_dec(x_50);
x_57 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_57, 0, x_48);
lean_ctor_set(x_57, 1, x_47);
lean_ctor_set(x_57, 2, x_51);
lean_ctor_set(x_57, 3, x_54);
lean_ctor_set(x_57, 4, x_53);
lean_ctor_set(x_57, 5, x_52);
lean_ctor_set(x_57, 6, x_49);
lean_ctor_set(x_57, 7, x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*8, x_56);
if (lean_is_scalar(x_45)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_45;
}
lean_ctor_set(x_58, 0, x_46);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
block_136:
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_44, 7);
lean_inc(x_61);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; size_t x_79; size_t x_80; size_t x_81; lean_object* x_82; uint8_t x_83; 
x_63 = lean_ctor_get(x_61, 0);
x_64 = lean_ctor_get(x_61, 1);
x_65 = lean_ctor_get(x_44, 1);
lean_inc(x_65);
x_66 = lean_box(0);
x_67 = lean_box(0);
x_68 = lean_ctor_get(x_44, 5);
lean_inc(x_68);
x_69 = lean_ctor_get(x_44, 0);
lean_inc(x_69);
x_70 = lean_unbox(x_66);
x_71 = lean_unbox(x_67);
x_72 = l_Lean_LocalContext_mkLocalDecl(x_65, x_43, x_60, x_40, x_70, x_71);
x_73 = lean_ctor_get(x_44, 2);
lean_inc(x_73);
x_74 = lean_ctor_get(x_44, 3);
lean_inc(x_74);
x_75 = lean_ctor_get(x_44, 4);
lean_inc(x_75);
lean_inc(x_46);
x_76 = lean_array_push(x_68, x_46);
x_77 = lean_ctor_get(x_44, 6);
lean_inc(x_77);
x_78 = lean_array_get_size(x_64);
x_79 = lean_usize_of_nat(x_78);
lean_dec(x_78);
x_80 = lean_usize_sub(x_79, x_33);
x_81 = lean_usize_land(x_30, x_80);
x_82 = lean_array_uget(x_64, x_81);
x_83 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(x_5, x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_84 = lean_nat_add(x_63, x_32);
lean_dec(x_63);
lean_inc(x_46);
x_85 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_85, 0, x_5);
lean_ctor_set(x_85, 1, x_46);
lean_ctor_set(x_85, 2, x_82);
x_86 = lean_array_uset(x_64, x_81, x_85);
x_87 = lean_unsigned_to_nat(2u);
x_88 = lean_nat_shiftl(x_84, x_87);
x_89 = lean_unsigned_to_nat(3u);
x_90 = lean_nat_div(x_88, x_89);
lean_dec(x_88);
x_91 = lean_array_get_size(x_86);
x_92 = lean_nat_dec_le(x_90, x_91);
lean_dec(x_91);
lean_dec(x_90);
if (x_92 == 0)
{
lean_object* x_93; 
x_93 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__3___redArg(x_86);
lean_ctor_set(x_61, 1, x_93);
lean_ctor_set(x_61, 0, x_84);
x_47 = x_72;
x_48 = x_69;
x_49 = x_77;
x_50 = x_44;
x_51 = x_73;
x_52 = x_76;
x_53 = x_75;
x_54 = x_74;
x_55 = x_61;
goto block_59;
}
else
{
lean_ctor_set(x_61, 1, x_86);
lean_ctor_set(x_61, 0, x_84);
x_47 = x_72;
x_48 = x_69;
x_49 = x_77;
x_50 = x_44;
x_51 = x_73;
x_52 = x_76;
x_53 = x_75;
x_54 = x_74;
x_55 = x_61;
goto block_59;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_box(0);
x_95 = lean_array_uset(x_64, x_81, x_94);
lean_inc(x_46);
x_96 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__6___redArg(x_5, x_46, x_82);
x_97 = lean_array_uset(x_95, x_81, x_96);
lean_ctor_set(x_61, 1, x_97);
x_47 = x_72;
x_48 = x_69;
x_49 = x_77;
x_50 = x_44;
x_51 = x_73;
x_52 = x_76;
x_53 = x_75;
x_54 = x_74;
x_55 = x_61;
goto block_59;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; size_t x_114; size_t x_115; size_t x_116; lean_object* x_117; uint8_t x_118; 
x_98 = lean_ctor_get(x_61, 0);
x_99 = lean_ctor_get(x_61, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_61);
x_100 = lean_ctor_get(x_44, 1);
lean_inc(x_100);
x_101 = lean_box(0);
x_102 = lean_box(0);
x_103 = lean_ctor_get(x_44, 5);
lean_inc(x_103);
x_104 = lean_ctor_get(x_44, 0);
lean_inc(x_104);
x_105 = lean_unbox(x_101);
x_106 = lean_unbox(x_102);
x_107 = l_Lean_LocalContext_mkLocalDecl(x_100, x_43, x_60, x_40, x_105, x_106);
x_108 = lean_ctor_get(x_44, 2);
lean_inc(x_108);
x_109 = lean_ctor_get(x_44, 3);
lean_inc(x_109);
x_110 = lean_ctor_get(x_44, 4);
lean_inc(x_110);
lean_inc(x_46);
x_111 = lean_array_push(x_103, x_46);
x_112 = lean_ctor_get(x_44, 6);
lean_inc(x_112);
x_113 = lean_array_get_size(x_99);
x_114 = lean_usize_of_nat(x_113);
lean_dec(x_113);
x_115 = lean_usize_sub(x_114, x_33);
x_116 = lean_usize_land(x_30, x_115);
x_117 = lean_array_uget(x_99, x_116);
x_118 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(x_5, x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_119 = lean_nat_add(x_98, x_32);
lean_dec(x_98);
lean_inc(x_46);
x_120 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_120, 0, x_5);
lean_ctor_set(x_120, 1, x_46);
lean_ctor_set(x_120, 2, x_117);
x_121 = lean_array_uset(x_99, x_116, x_120);
x_122 = lean_unsigned_to_nat(2u);
x_123 = lean_nat_shiftl(x_119, x_122);
x_124 = lean_unsigned_to_nat(3u);
x_125 = lean_nat_div(x_123, x_124);
lean_dec(x_123);
x_126 = lean_array_get_size(x_121);
x_127 = lean_nat_dec_le(x_125, x_126);
lean_dec(x_126);
lean_dec(x_125);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__3___redArg(x_121);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_119);
lean_ctor_set(x_129, 1, x_128);
x_47 = x_107;
x_48 = x_104;
x_49 = x_112;
x_50 = x_44;
x_51 = x_108;
x_52 = x_111;
x_53 = x_110;
x_54 = x_109;
x_55 = x_129;
goto block_59;
}
else
{
lean_object* x_130; 
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_119);
lean_ctor_set(x_130, 1, x_121);
x_47 = x_107;
x_48 = x_104;
x_49 = x_112;
x_50 = x_44;
x_51 = x_108;
x_52 = x_111;
x_53 = x_110;
x_54 = x_109;
x_55 = x_130;
goto block_59;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_131 = lean_box(0);
x_132 = lean_array_uset(x_99, x_116, x_131);
lean_inc(x_46);
x_133 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__6___redArg(x_5, x_46, x_117);
x_134 = lean_array_uset(x_132, x_116, x_133);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_98);
lean_ctor_set(x_135, 1, x_134);
x_47 = x_107;
x_48 = x_104;
x_49 = x_112;
x_50 = x_44;
x_51 = x_108;
x_52 = x_111;
x_53 = x_110;
x_54 = x_109;
x_55 = x_135;
goto block_59;
}
}
}
}
else
{
lean_object* x_144; 
lean_dec(x_7);
lean_dec(x_5);
x_144 = lean_ctor_get(x_37, 0);
lean_inc(x_144);
lean_dec(x_37);
lean_ctor_set(x_12, 0, x_144);
return x_12;
}
}
}
else
{
lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_145 = lean_ctor_get(x_12, 0);
x_146 = lean_ctor_get(x_12, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_12);
x_147 = lean_expr_eqv(x_1, x_145);
lean_dec(x_1);
if (x_147 == 0)
{
lean_dec(x_7);
lean_dec(x_5);
x_1 = x_145;
x_2 = x_146;
goto _start;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; uint64_t x_152; lean_object* x_153; uint64_t x_154; uint64_t x_155; uint64_t x_156; lean_object* x_157; uint64_t x_158; uint64_t x_159; uint64_t x_160; size_t x_161; size_t x_162; lean_object* x_163; size_t x_164; size_t x_165; size_t x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_145);
x_149 = lean_ctor_get(x_146, 7);
lean_inc(x_149);
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
x_151 = lean_array_get_size(x_150);
x_152 = l___private_Lean_Expr_0__Lean_hashMVarId____x40_Lean_Expr___hyg_1984_(x_5);
x_153 = lean_unsigned_to_nat(32u);
x_154 = lean_uint64_of_nat(x_153);
x_155 = lean_uint64_shift_right(x_152, x_154);
x_156 = lean_uint64_xor(x_152, x_155);
x_157 = lean_unsigned_to_nat(16u);
x_158 = lean_uint64_of_nat(x_157);
x_159 = lean_uint64_shift_right(x_156, x_158);
x_160 = lean_uint64_xor(x_156, x_159);
x_161 = lean_uint64_to_usize(x_160);
x_162 = lean_usize_of_nat(x_151);
lean_dec(x_151);
x_163 = lean_unsigned_to_nat(1u);
x_164 = lean_usize_of_nat(x_163);
x_165 = lean_usize_sub(x_162, x_164);
x_166 = lean_usize_land(x_161, x_165);
x_167 = lean_array_uget(x_150, x_166);
lean_dec(x_150);
x_168 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__1___redArg(x_5, x_167);
lean_dec(x_167);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_191; lean_object* x_233; uint8_t x_234; 
x_169 = lean_ctor_get(x_7, 2);
lean_inc(x_169);
x_170 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_169, x_146);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = l_Lean_Meta_AbstractMVars_mkFreshFVarId(x_172);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_176 = x_173;
} else {
 lean_dec_ref(x_173);
 x_176 = lean_box(0);
}
lean_inc(x_174);
x_177 = l_Lean_Expr_fvar___override(x_174);
x_233 = lean_ctor_get(x_7, 0);
lean_inc(x_233);
lean_dec(x_7);
x_234 = l_Lean_Name_isAnonymous(x_233);
if (x_234 == 0)
{
x_191 = x_233;
goto block_232;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_233);
x_235 = lean_mk_string_unchecked("x", 1, 1);
x_236 = l_Lean_Name_mkStr1(x_235);
x_237 = lean_ctor_get(x_175, 5);
lean_inc(x_237);
x_238 = lean_array_get_size(x_237);
lean_dec(x_237);
x_239 = lean_name_append_index_after(x_236, x_238);
x_191 = x_239;
goto block_232;
}
block_190:
{
uint8_t x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get_uint8(x_181, sizeof(void*)*8);
lean_dec(x_181);
x_188 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_188, 0, x_179);
lean_ctor_set(x_188, 1, x_178);
lean_ctor_set(x_188, 2, x_182);
lean_ctor_set(x_188, 3, x_185);
lean_ctor_set(x_188, 4, x_184);
lean_ctor_set(x_188, 5, x_183);
lean_ctor_set(x_188, 6, x_180);
lean_ctor_set(x_188, 7, x_186);
lean_ctor_set_uint8(x_188, sizeof(void*)*8, x_187);
if (lean_is_scalar(x_176)) {
 x_189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_189 = x_176;
}
lean_ctor_set(x_189, 0, x_177);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
block_232:
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; uint8_t x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; size_t x_210; size_t x_211; size_t x_212; lean_object* x_213; uint8_t x_214; 
x_192 = lean_ctor_get(x_175, 7);
lean_inc(x_192);
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
x_196 = lean_ctor_get(x_175, 1);
lean_inc(x_196);
x_197 = lean_box(0);
x_198 = lean_box(0);
x_199 = lean_ctor_get(x_175, 5);
lean_inc(x_199);
x_200 = lean_ctor_get(x_175, 0);
lean_inc(x_200);
x_201 = lean_unbox(x_197);
x_202 = lean_unbox(x_198);
x_203 = l_Lean_LocalContext_mkLocalDecl(x_196, x_174, x_191, x_171, x_201, x_202);
x_204 = lean_ctor_get(x_175, 2);
lean_inc(x_204);
x_205 = lean_ctor_get(x_175, 3);
lean_inc(x_205);
x_206 = lean_ctor_get(x_175, 4);
lean_inc(x_206);
lean_inc(x_177);
x_207 = lean_array_push(x_199, x_177);
x_208 = lean_ctor_get(x_175, 6);
lean_inc(x_208);
x_209 = lean_array_get_size(x_194);
x_210 = lean_usize_of_nat(x_209);
lean_dec(x_209);
x_211 = lean_usize_sub(x_210, x_164);
x_212 = lean_usize_land(x_161, x_211);
x_213 = lean_array_uget(x_194, x_212);
x_214 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(x_5, x_213);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_215 = lean_nat_add(x_193, x_163);
lean_dec(x_193);
lean_inc(x_177);
x_216 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_216, 0, x_5);
lean_ctor_set(x_216, 1, x_177);
lean_ctor_set(x_216, 2, x_213);
x_217 = lean_array_uset(x_194, x_212, x_216);
x_218 = lean_unsigned_to_nat(2u);
x_219 = lean_nat_shiftl(x_215, x_218);
x_220 = lean_unsigned_to_nat(3u);
x_221 = lean_nat_div(x_219, x_220);
lean_dec(x_219);
x_222 = lean_array_get_size(x_217);
x_223 = lean_nat_dec_le(x_221, x_222);
lean_dec(x_222);
lean_dec(x_221);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; 
x_224 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__3___redArg(x_217);
if (lean_is_scalar(x_195)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_195;
}
lean_ctor_set(x_225, 0, x_215);
lean_ctor_set(x_225, 1, x_224);
x_178 = x_203;
x_179 = x_200;
x_180 = x_208;
x_181 = x_175;
x_182 = x_204;
x_183 = x_207;
x_184 = x_206;
x_185 = x_205;
x_186 = x_225;
goto block_190;
}
else
{
lean_object* x_226; 
if (lean_is_scalar(x_195)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_195;
}
lean_ctor_set(x_226, 0, x_215);
lean_ctor_set(x_226, 1, x_217);
x_178 = x_203;
x_179 = x_200;
x_180 = x_208;
x_181 = x_175;
x_182 = x_204;
x_183 = x_207;
x_184 = x_206;
x_185 = x_205;
x_186 = x_226;
goto block_190;
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_227 = lean_box(0);
x_228 = lean_array_uset(x_194, x_212, x_227);
lean_inc(x_177);
x_229 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__6___redArg(x_5, x_177, x_213);
x_230 = lean_array_uset(x_228, x_212, x_229);
if (lean_is_scalar(x_195)) {
 x_231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_231 = x_195;
}
lean_ctor_set(x_231, 0, x_193);
lean_ctor_set(x_231, 1, x_230);
x_178 = x_203;
x_179 = x_200;
x_180 = x_208;
x_181 = x_175;
x_182 = x_204;
x_183 = x_207;
x_184 = x_206;
x_185 = x_205;
x_186 = x_231;
goto block_190;
}
}
}
else
{
lean_object* x_240; lean_object* x_241; 
lean_dec(x_7);
lean_dec(x_5);
x_240 = lean_ctor_get(x_168, 0);
lean_inc(x_240);
lean_dec(x_168);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_146);
return x_241;
}
}
}
}
}
case 3:
{
lean_object* x_242; lean_object* x_243; uint8_t x_244; 
x_242 = lean_ctor_get(x_1, 0);
lean_inc(x_242);
lean_inc(x_242);
x_243 = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(x_242, x_2);
x_244 = !lean_is_exclusive(x_243);
if (x_244 == 0)
{
lean_object* x_245; size_t x_246; size_t x_247; uint8_t x_248; 
x_245 = lean_ctor_get(x_243, 0);
x_246 = lean_ptr_addr(x_242);
lean_dec(x_242);
x_247 = lean_ptr_addr(x_245);
x_248 = lean_usize_dec_eq(x_246, x_247);
if (x_248 == 0)
{
lean_object* x_249; 
lean_dec(x_1);
x_249 = l_Lean_Expr_sort___override(x_245);
lean_ctor_set(x_243, 0, x_249);
return x_243;
}
else
{
lean_dec(x_245);
lean_ctor_set(x_243, 0, x_1);
return x_243;
}
}
else
{
lean_object* x_250; lean_object* x_251; size_t x_252; size_t x_253; uint8_t x_254; 
x_250 = lean_ctor_get(x_243, 0);
x_251 = lean_ctor_get(x_243, 1);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_243);
x_252 = lean_ptr_addr(x_242);
lean_dec(x_242);
x_253 = lean_ptr_addr(x_250);
x_254 = lean_usize_dec_eq(x_252, x_253);
if (x_254 == 0)
{
lean_object* x_255; lean_object* x_256; 
lean_dec(x_1);
x_255 = l_Lean_Expr_sort___override(x_250);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_251);
return x_256;
}
else
{
lean_object* x_257; 
lean_dec(x_250);
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_1);
lean_ctor_set(x_257, 1, x_251);
return x_257;
}
}
}
case 4:
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; uint8_t x_262; 
x_258 = lean_ctor_get(x_1, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_1, 1);
lean_inc(x_259);
x_260 = lean_box(0);
lean_inc(x_259);
x_261 = l_List_mapM_loop___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__7(x_259, x_260, x_2);
x_262 = !lean_is_exclusive(x_261);
if (x_262 == 0)
{
lean_object* x_263; uint8_t x_264; 
x_263 = lean_ctor_get(x_261, 0);
x_264 = l_ptrEqList___redArg(x_259, x_263);
lean_dec(x_259);
if (x_264 == 0)
{
lean_object* x_265; 
lean_dec(x_1);
x_265 = l_Lean_Expr_const___override(x_258, x_263);
lean_ctor_set(x_261, 0, x_265);
return x_261;
}
else
{
lean_dec(x_263);
lean_dec(x_258);
lean_ctor_set(x_261, 0, x_1);
return x_261;
}
}
else
{
lean_object* x_266; lean_object* x_267; uint8_t x_268; 
x_266 = lean_ctor_get(x_261, 0);
x_267 = lean_ctor_get(x_261, 1);
lean_inc(x_267);
lean_inc(x_266);
lean_dec(x_261);
x_268 = l_ptrEqList___redArg(x_259, x_266);
lean_dec(x_259);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; 
lean_dec(x_1);
x_269 = l_Lean_Expr_const___override(x_258, x_266);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_267);
return x_270;
}
else
{
lean_object* x_271; 
lean_dec(x_266);
lean_dec(x_258);
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_1);
lean_ctor_set(x_271, 1, x_267);
return x_271;
}
}
}
case 5:
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; uint8_t x_281; size_t x_286; size_t x_287; uint8_t x_288; 
x_272 = lean_ctor_get(x_1, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_1, 1);
lean_inc(x_273);
lean_inc(x_272);
x_274 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_272, x_2);
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_274, 1);
lean_inc(x_276);
lean_dec(x_274);
lean_inc(x_273);
x_277 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_273, x_276);
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_277, 1);
lean_inc(x_279);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 x_280 = x_277;
} else {
 lean_dec_ref(x_277);
 x_280 = lean_box(0);
}
x_286 = lean_ptr_addr(x_272);
lean_dec(x_272);
x_287 = lean_ptr_addr(x_275);
x_288 = lean_usize_dec_eq(x_286, x_287);
if (x_288 == 0)
{
lean_dec(x_273);
x_281 = x_288;
goto block_285;
}
else
{
size_t x_289; size_t x_290; uint8_t x_291; 
x_289 = lean_ptr_addr(x_273);
lean_dec(x_273);
x_290 = lean_ptr_addr(x_278);
x_291 = lean_usize_dec_eq(x_289, x_290);
x_281 = x_291;
goto block_285;
}
block_285:
{
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; 
lean_dec(x_1);
x_282 = l_Lean_Expr_app___override(x_275, x_278);
if (lean_is_scalar(x_280)) {
 x_283 = lean_alloc_ctor(0, 2, 0);
} else {
 x_283 = x_280;
}
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_279);
return x_283;
}
else
{
lean_object* x_284; 
lean_dec(x_278);
lean_dec(x_275);
if (lean_is_scalar(x_280)) {
 x_284 = lean_alloc_ctor(0, 2, 0);
} else {
 x_284 = x_280;
}
lean_ctor_set(x_284, 0, x_1);
lean_ctor_set(x_284, 1, x_279);
return x_284;
}
}
}
case 6:
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_292 = lean_ctor_get(x_1, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_1, 1);
lean_inc(x_293);
x_294 = lean_ctor_get(x_1, 2);
lean_inc(x_294);
x_295 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
lean_inc(x_293);
x_296 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_293, x_2);
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec(x_296);
lean_inc(x_294);
x_299 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_294, x_298);
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 x_302 = x_299;
} else {
 lean_dec_ref(x_299);
 x_302 = lean_box(0);
}
x_303 = l_Lean_Expr_lam___override(x_292, x_293, x_294, x_295);
if (lean_obj_tag(x_303) == 6)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; uint8_t x_307; uint8_t x_308; size_t x_316; size_t x_317; uint8_t x_318; 
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_303, 1);
lean_inc(x_305);
x_306 = lean_ctor_get(x_303, 2);
lean_inc(x_306);
x_307 = lean_ctor_get_uint8(x_303, sizeof(void*)*3 + 8);
x_316 = lean_ptr_addr(x_305);
lean_dec(x_305);
x_317 = lean_ptr_addr(x_297);
x_318 = lean_usize_dec_eq(x_316, x_317);
if (x_318 == 0)
{
lean_dec(x_306);
x_308 = x_318;
goto block_315;
}
else
{
size_t x_319; size_t x_320; uint8_t x_321; 
x_319 = lean_ptr_addr(x_306);
lean_dec(x_306);
x_320 = lean_ptr_addr(x_300);
x_321 = lean_usize_dec_eq(x_319, x_320);
x_308 = x_321;
goto block_315;
}
block_315:
{
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; 
lean_dec(x_303);
x_309 = l_Lean_Expr_lam___override(x_304, x_297, x_300, x_295);
if (lean_is_scalar(x_302)) {
 x_310 = lean_alloc_ctor(0, 2, 0);
} else {
 x_310 = x_302;
}
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_310, 1, x_301);
return x_310;
}
else
{
uint8_t x_311; 
x_311 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_307, x_295);
if (x_311 == 0)
{
lean_object* x_312; lean_object* x_313; 
lean_dec(x_303);
x_312 = l_Lean_Expr_lam___override(x_304, x_297, x_300, x_295);
if (lean_is_scalar(x_302)) {
 x_313 = lean_alloc_ctor(0, 2, 0);
} else {
 x_313 = x_302;
}
lean_ctor_set(x_313, 0, x_312);
lean_ctor_set(x_313, 1, x_301);
return x_313;
}
else
{
lean_object* x_314; 
lean_dec(x_304);
lean_dec(x_300);
lean_dec(x_297);
if (lean_is_scalar(x_302)) {
 x_314 = lean_alloc_ctor(0, 2, 0);
} else {
 x_314 = x_302;
}
lean_ctor_set(x_314, 0, x_303);
lean_ctor_set(x_314, 1, x_301);
return x_314;
}
}
}
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
lean_dec(x_303);
lean_dec(x_300);
lean_dec(x_297);
x_322 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_323 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateLambda!Impl", 48, 48);
x_324 = lean_unsigned_to_nat(1848u);
x_325 = lean_unsigned_to_nat(19u);
x_326 = lean_mk_string_unchecked("lambda expected", 15, 15);
x_327 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_322, x_323, x_324, x_325, x_326);
lean_dec(x_326);
lean_dec(x_323);
lean_dec(x_322);
x_328 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_327);
if (lean_is_scalar(x_302)) {
 x_329 = lean_alloc_ctor(0, 2, 0);
} else {
 x_329 = x_302;
}
lean_ctor_set(x_329, 0, x_328);
lean_ctor_set(x_329, 1, x_301);
return x_329;
}
}
case 7:
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; uint8_t x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_330 = lean_ctor_get(x_1, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_1, 1);
lean_inc(x_331);
x_332 = lean_ctor_get(x_1, 2);
lean_inc(x_332);
x_333 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
lean_inc(x_331);
x_334 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_331, x_2);
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_334, 1);
lean_inc(x_336);
lean_dec(x_334);
lean_inc(x_332);
x_337 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_332, x_336);
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_337, 1);
lean_inc(x_339);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 x_340 = x_337;
} else {
 lean_dec_ref(x_337);
 x_340 = lean_box(0);
}
x_341 = l_Lean_Expr_forallE___override(x_330, x_331, x_332, x_333);
if (lean_obj_tag(x_341) == 7)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; uint8_t x_345; uint8_t x_346; size_t x_354; size_t x_355; uint8_t x_356; 
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_341, 1);
lean_inc(x_343);
x_344 = lean_ctor_get(x_341, 2);
lean_inc(x_344);
x_345 = lean_ctor_get_uint8(x_341, sizeof(void*)*3 + 8);
x_354 = lean_ptr_addr(x_343);
lean_dec(x_343);
x_355 = lean_ptr_addr(x_335);
x_356 = lean_usize_dec_eq(x_354, x_355);
if (x_356 == 0)
{
lean_dec(x_344);
x_346 = x_356;
goto block_353;
}
else
{
size_t x_357; size_t x_358; uint8_t x_359; 
x_357 = lean_ptr_addr(x_344);
lean_dec(x_344);
x_358 = lean_ptr_addr(x_338);
x_359 = lean_usize_dec_eq(x_357, x_358);
x_346 = x_359;
goto block_353;
}
block_353:
{
if (x_346 == 0)
{
lean_object* x_347; lean_object* x_348; 
lean_dec(x_341);
x_347 = l_Lean_Expr_forallE___override(x_342, x_335, x_338, x_333);
if (lean_is_scalar(x_340)) {
 x_348 = lean_alloc_ctor(0, 2, 0);
} else {
 x_348 = x_340;
}
lean_ctor_set(x_348, 0, x_347);
lean_ctor_set(x_348, 1, x_339);
return x_348;
}
else
{
uint8_t x_349; 
x_349 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_345, x_333);
if (x_349 == 0)
{
lean_object* x_350; lean_object* x_351; 
lean_dec(x_341);
x_350 = l_Lean_Expr_forallE___override(x_342, x_335, x_338, x_333);
if (lean_is_scalar(x_340)) {
 x_351 = lean_alloc_ctor(0, 2, 0);
} else {
 x_351 = x_340;
}
lean_ctor_set(x_351, 0, x_350);
lean_ctor_set(x_351, 1, x_339);
return x_351;
}
else
{
lean_object* x_352; 
lean_dec(x_342);
lean_dec(x_338);
lean_dec(x_335);
if (lean_is_scalar(x_340)) {
 x_352 = lean_alloc_ctor(0, 2, 0);
} else {
 x_352 = x_340;
}
lean_ctor_set(x_352, 0, x_341);
lean_ctor_set(x_352, 1, x_339);
return x_352;
}
}
}
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
lean_dec(x_341);
lean_dec(x_338);
lean_dec(x_335);
x_360 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_361 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateForall!Impl", 48, 48);
x_362 = lean_unsigned_to_nat(1828u);
x_363 = lean_unsigned_to_nat(23u);
x_364 = lean_mk_string_unchecked("forall expected", 15, 15);
x_365 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_360, x_361, x_362, x_363, x_364);
lean_dec(x_364);
lean_dec(x_361);
lean_dec(x_360);
x_366 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_365);
if (lean_is_scalar(x_340)) {
 x_367 = lean_alloc_ctor(0, 2, 0);
} else {
 x_367 = x_340;
}
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_339);
return x_367;
}
}
case 8:
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; uint8_t x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; uint8_t x_387; size_t x_393; size_t x_394; uint8_t x_395; 
x_368 = lean_ctor_get(x_1, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_1, 1);
lean_inc(x_369);
x_370 = lean_ctor_get(x_1, 2);
lean_inc(x_370);
x_371 = lean_ctor_get(x_1, 3);
lean_inc(x_371);
x_372 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
lean_inc(x_369);
x_373 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_369, x_2);
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_373, 1);
lean_inc(x_375);
lean_dec(x_373);
lean_inc(x_370);
x_376 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_370, x_375);
x_377 = lean_ctor_get(x_376, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_376, 1);
lean_inc(x_378);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 x_379 = x_376;
} else {
 lean_dec_ref(x_376);
 x_379 = lean_box(0);
}
lean_inc(x_371);
x_380 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_371, x_378);
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_380, 1);
lean_inc(x_382);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 x_383 = x_380;
} else {
 lean_dec_ref(x_380);
 x_383 = lean_box(0);
}
x_393 = lean_ptr_addr(x_369);
lean_dec(x_369);
x_394 = lean_ptr_addr(x_374);
x_395 = lean_usize_dec_eq(x_393, x_394);
if (x_395 == 0)
{
lean_dec(x_370);
x_387 = x_395;
goto block_392;
}
else
{
size_t x_396; size_t x_397; uint8_t x_398; 
x_396 = lean_ptr_addr(x_370);
lean_dec(x_370);
x_397 = lean_ptr_addr(x_377);
x_398 = lean_usize_dec_eq(x_396, x_397);
x_387 = x_398;
goto block_392;
}
block_386:
{
lean_object* x_384; lean_object* x_385; 
x_384 = l_Lean_Expr_letE___override(x_368, x_374, x_377, x_381, x_372);
if (lean_is_scalar(x_383)) {
 x_385 = lean_alloc_ctor(0, 2, 0);
} else {
 x_385 = x_383;
}
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_382);
return x_385;
}
block_392:
{
if (x_387 == 0)
{
lean_dec(x_379);
lean_dec(x_371);
lean_dec(x_1);
goto block_386;
}
else
{
size_t x_388; size_t x_389; uint8_t x_390; 
x_388 = lean_ptr_addr(x_371);
lean_dec(x_371);
x_389 = lean_ptr_addr(x_381);
x_390 = lean_usize_dec_eq(x_388, x_389);
if (x_390 == 0)
{
lean_dec(x_379);
lean_dec(x_1);
goto block_386;
}
else
{
lean_object* x_391; 
lean_dec(x_383);
lean_dec(x_381);
lean_dec(x_377);
lean_dec(x_374);
lean_dec(x_368);
if (lean_is_scalar(x_379)) {
 x_391 = lean_alloc_ctor(0, 2, 0);
} else {
 x_391 = x_379;
}
lean_ctor_set(x_391, 0, x_1);
lean_ctor_set(x_391, 1, x_382);
return x_391;
}
}
}
}
case 10:
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; 
x_399 = lean_ctor_get(x_1, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_1, 1);
lean_inc(x_400);
lean_inc(x_400);
x_401 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_400, x_2);
x_402 = !lean_is_exclusive(x_401);
if (x_402 == 0)
{
lean_object* x_403; size_t x_404; size_t x_405; uint8_t x_406; 
x_403 = lean_ctor_get(x_401, 0);
x_404 = lean_ptr_addr(x_400);
lean_dec(x_400);
x_405 = lean_ptr_addr(x_403);
x_406 = lean_usize_dec_eq(x_404, x_405);
if (x_406 == 0)
{
lean_object* x_407; 
lean_dec(x_1);
x_407 = l_Lean_Expr_mdata___override(x_399, x_403);
lean_ctor_set(x_401, 0, x_407);
return x_401;
}
else
{
lean_dec(x_403);
lean_dec(x_399);
lean_ctor_set(x_401, 0, x_1);
return x_401;
}
}
else
{
lean_object* x_408; lean_object* x_409; size_t x_410; size_t x_411; uint8_t x_412; 
x_408 = lean_ctor_get(x_401, 0);
x_409 = lean_ctor_get(x_401, 1);
lean_inc(x_409);
lean_inc(x_408);
lean_dec(x_401);
x_410 = lean_ptr_addr(x_400);
lean_dec(x_400);
x_411 = lean_ptr_addr(x_408);
x_412 = lean_usize_dec_eq(x_410, x_411);
if (x_412 == 0)
{
lean_object* x_413; lean_object* x_414; 
lean_dec(x_1);
x_413 = l_Lean_Expr_mdata___override(x_399, x_408);
x_414 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_414, 0, x_413);
lean_ctor_set(x_414, 1, x_409);
return x_414;
}
else
{
lean_object* x_415; 
lean_dec(x_408);
lean_dec(x_399);
x_415 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_415, 0, x_1);
lean_ctor_set(x_415, 1, x_409);
return x_415;
}
}
}
case 11:
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; uint8_t x_420; 
x_416 = lean_ctor_get(x_1, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_1, 1);
lean_inc(x_417);
x_418 = lean_ctor_get(x_1, 2);
lean_inc(x_418);
lean_inc(x_418);
x_419 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_418, x_2);
x_420 = !lean_is_exclusive(x_419);
if (x_420 == 0)
{
lean_object* x_421; size_t x_422; size_t x_423; uint8_t x_424; 
x_421 = lean_ctor_get(x_419, 0);
x_422 = lean_ptr_addr(x_418);
lean_dec(x_418);
x_423 = lean_ptr_addr(x_421);
x_424 = lean_usize_dec_eq(x_422, x_423);
if (x_424 == 0)
{
lean_object* x_425; 
lean_dec(x_1);
x_425 = l_Lean_Expr_proj___override(x_416, x_417, x_421);
lean_ctor_set(x_419, 0, x_425);
return x_419;
}
else
{
lean_dec(x_421);
lean_dec(x_417);
lean_dec(x_416);
lean_ctor_set(x_419, 0, x_1);
return x_419;
}
}
else
{
lean_object* x_426; lean_object* x_427; size_t x_428; size_t x_429; uint8_t x_430; 
x_426 = lean_ctor_get(x_419, 0);
x_427 = lean_ctor_get(x_419, 1);
lean_inc(x_427);
lean_inc(x_426);
lean_dec(x_419);
x_428 = lean_ptr_addr(x_418);
lean_dec(x_418);
x_429 = lean_ptr_addr(x_426);
x_430 = lean_usize_dec_eq(x_428, x_429);
if (x_430 == 0)
{
lean_object* x_431; lean_object* x_432; 
lean_dec(x_1);
x_431 = l_Lean_Expr_proj___override(x_416, x_417, x_426);
x_432 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_432, 0, x_431);
lean_ctor_set(x_432, 1, x_427);
return x_432;
}
else
{
lean_object* x_433; 
lean_dec(x_426);
lean_dec(x_417);
lean_dec(x_416);
x_433 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_433, 0, x_1);
lean_ctor_set(x_433, 1, x_427);
return x_433;
}
}
}
default: 
{
lean_object* x_434; 
x_434 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_434, 0, x_1);
lean_ctor_set(x_434, 1, x_2);
return x_434;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_AbstractMVars_abstractExprMVars_spec__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractMVars___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_1, x_4, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_st_ref_get(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_5, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_ctor_get(x_3, 2);
x_19 = lean_ctor_get(x_15, 2);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_mk_empty_array_with_capacity(x_20);
x_22 = lean_unsigned_to_nat(8u);
x_23 = lean_unsigned_to_nat(2u);
x_24 = lean_nat_shiftl(x_22, x_23);
x_25 = lean_unsigned_to_nat(3u);
x_26 = lean_nat_div(x_24, x_25);
lean_dec(x_24);
x_27 = l_Nat_nextPowerOfTwo(x_26);
lean_dec(x_26);
x_28 = lean_box(0);
x_29 = lean_mk_array(x_27, x_28);
lean_ctor_set(x_13, 1, x_29);
lean_ctor_set(x_13, 0, x_20);
lean_inc(x_13);
lean_inc(x_21);
lean_inc(x_18);
x_30 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_30, 0, x_19);
lean_ctor_set(x_30, 1, x_18);
lean_ctor_set(x_30, 2, x_17);
lean_ctor_set(x_30, 3, x_20);
lean_ctor_set(x_30, 4, x_21);
lean_ctor_set(x_30, 5, x_21);
lean_ctor_set(x_30, 6, x_13);
lean_ctor_set(x_30, 7, x_13);
lean_ctor_set_uint8(x_30, sizeof(void*)*8, x_2);
x_31 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_8, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_st_ref_take(x_5, x_16);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_33, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_35, 3);
lean_inc(x_40);
x_41 = lean_ctor_get(x_35, 4);
lean_inc(x_41);
x_42 = lean_ctor_get(x_35, 5);
lean_inc(x_42);
x_43 = lean_ctor_get(x_35, 6);
lean_inc(x_43);
x_44 = lean_ctor_get(x_35, 7);
lean_inc(x_44);
lean_dec(x_35);
x_45 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_39);
lean_ctor_set(x_45, 2, x_37);
lean_ctor_set(x_45, 3, x_40);
lean_ctor_set(x_45, 4, x_41);
lean_ctor_set(x_45, 5, x_42);
lean_ctor_set(x_45, 6, x_43);
lean_ctor_set(x_45, 7, x_44);
x_46 = lean_st_ref_set(x_5, x_45, x_36);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_st_ref_take(x_4, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_ctor_get(x_33, 2);
lean_inc(x_51);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_49, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_49, 3);
lean_inc(x_54);
x_55 = lean_ctor_get(x_49, 4);
lean_inc(x_55);
lean_dec(x_49);
x_56 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_56, 0, x_51);
lean_ctor_set(x_56, 1, x_52);
lean_ctor_set(x_56, 2, x_53);
lean_ctor_set(x_56, 3, x_54);
lean_ctor_set(x_56, 4, x_55);
x_57 = lean_st_ref_set(x_4, x_56, x_50);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
x_60 = lean_ctor_get(x_33, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_33, 5);
lean_inc(x_61);
lean_inc(x_61);
x_62 = l_Lean_LocalContext_mkLambda(x_60, x_61, x_32);
lean_dec(x_32);
x_63 = lean_ctor_get(x_33, 4);
lean_inc(x_63);
lean_dec(x_33);
x_64 = lean_array_get_size(x_61);
lean_dec(x_61);
x_65 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_65, 2, x_62);
lean_ctor_set(x_57, 0, x_65);
return x_57;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_66 = lean_ctor_get(x_57, 1);
lean_inc(x_66);
lean_dec(x_57);
x_67 = lean_ctor_get(x_33, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_33, 5);
lean_inc(x_68);
lean_inc(x_68);
x_69 = l_Lean_LocalContext_mkLambda(x_67, x_68, x_32);
lean_dec(x_32);
x_70 = lean_ctor_get(x_33, 4);
lean_inc(x_70);
lean_dec(x_33);
x_71 = lean_array_get_size(x_68);
lean_dec(x_68);
x_72 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_72, 2, x_69);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_66);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_74 = lean_ctor_get(x_13, 0);
x_75 = lean_ctor_get(x_13, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_13);
x_76 = lean_ctor_get(x_11, 0);
lean_inc(x_76);
lean_dec(x_11);
x_77 = lean_ctor_get(x_3, 2);
x_78 = lean_ctor_get(x_74, 2);
lean_inc(x_78);
lean_dec(x_74);
x_79 = lean_unsigned_to_nat(0u);
x_80 = lean_mk_empty_array_with_capacity(x_79);
x_81 = lean_unsigned_to_nat(8u);
x_82 = lean_unsigned_to_nat(2u);
x_83 = lean_nat_shiftl(x_81, x_82);
x_84 = lean_unsigned_to_nat(3u);
x_85 = lean_nat_div(x_83, x_84);
lean_dec(x_83);
x_86 = l_Nat_nextPowerOfTwo(x_85);
lean_dec(x_85);
x_87 = lean_box(0);
x_88 = lean_mk_array(x_86, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_79);
lean_ctor_set(x_89, 1, x_88);
lean_inc(x_89);
lean_inc(x_80);
lean_inc(x_77);
x_90 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_90, 0, x_78);
lean_ctor_set(x_90, 1, x_77);
lean_ctor_set(x_90, 2, x_76);
lean_ctor_set(x_90, 3, x_79);
lean_ctor_set(x_90, 4, x_80);
lean_ctor_set(x_90, 5, x_80);
lean_ctor_set(x_90, 6, x_89);
lean_ctor_set(x_90, 7, x_89);
lean_ctor_set_uint8(x_90, sizeof(void*)*8, x_2);
x_91 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_8, x_90);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_st_ref_take(x_5, x_75);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_ctor_get(x_93, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_95, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_95, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_95, 3);
lean_inc(x_100);
x_101 = lean_ctor_get(x_95, 4);
lean_inc(x_101);
x_102 = lean_ctor_get(x_95, 5);
lean_inc(x_102);
x_103 = lean_ctor_get(x_95, 6);
lean_inc(x_103);
x_104 = lean_ctor_get(x_95, 7);
lean_inc(x_104);
lean_dec(x_95);
x_105 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_105, 0, x_98);
lean_ctor_set(x_105, 1, x_99);
lean_ctor_set(x_105, 2, x_97);
lean_ctor_set(x_105, 3, x_100);
lean_ctor_set(x_105, 4, x_101);
lean_ctor_set(x_105, 5, x_102);
lean_ctor_set(x_105, 6, x_103);
lean_ctor_set(x_105, 7, x_104);
x_106 = lean_st_ref_set(x_5, x_105, x_96);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_108 = lean_st_ref_take(x_4, x_107);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_ctor_get(x_93, 2);
lean_inc(x_111);
x_112 = lean_ctor_get(x_109, 1);
lean_inc(x_112);
x_113 = lean_ctor_get(x_109, 2);
lean_inc(x_113);
x_114 = lean_ctor_get(x_109, 3);
lean_inc(x_114);
x_115 = lean_ctor_get(x_109, 4);
lean_inc(x_115);
lean_dec(x_109);
x_116 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_116, 0, x_111);
lean_ctor_set(x_116, 1, x_112);
lean_ctor_set(x_116, 2, x_113);
lean_ctor_set(x_116, 3, x_114);
lean_ctor_set(x_116, 4, x_115);
x_117 = lean_st_ref_set(x_4, x_116, x_110);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_119 = x_117;
} else {
 lean_dec_ref(x_117);
 x_119 = lean_box(0);
}
x_120 = lean_ctor_get(x_93, 1);
lean_inc(x_120);
x_121 = lean_ctor_get(x_93, 5);
lean_inc(x_121);
lean_inc(x_121);
x_122 = l_Lean_LocalContext_mkLambda(x_120, x_121, x_92);
lean_dec(x_92);
x_123 = lean_ctor_get(x_93, 4);
lean_inc(x_123);
lean_dec(x_93);
x_124 = lean_array_get_size(x_121);
lean_dec(x_121);
x_125 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
lean_ctor_set(x_125, 2, x_122);
if (lean_is_scalar(x_119)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_119;
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_118);
return x_126;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractMVars(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_abstractMVars___redArg(x_1, x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractMVars___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l_Lean_Meta_abstractMVars___redArg(x_1, x_7, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_abstractMVars(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_openAbstractMVarsResult_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_2, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_11 = l_Lean_Meta_mkFreshLevelMVar(x_4, x_5, x_6, x_7, x_8);
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
x_8 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_openAbstractMVarsResult(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; size_t x_8; lean_object* x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_array_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_usize_of_nat(x_9);
lean_inc(x_7);
x_11 = l_Array_mapMUnsafe_map___at___Lean_Meta_openAbstractMVarsResult_spec__0(x_8, x_10, x_7, x_2, x_3, x_4, x_5, x_6);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
x_15 = l_Lean_Expr_instantiateLevelParamsArray(x_14, x_7, x_12);
lean_dec(x_14);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Lean_Meta_lambdaMetaTelescope(x_15, x_17, x_2, x_3, x_4, x_5, x_13);
lean_dec(x_17);
lean_dec(x_15);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_openAbstractMVarsResult_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at___Lean_Meta_openAbstractMVarsResult_spec__0(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_openAbstractMVarsResult___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_openAbstractMVarsResult(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_AbstractMVars(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_AbstractMVars_instMonadMCtxM = _init_l_Lean_Meta_AbstractMVars_instMonadMCtxM();
lean_mark_persistent(l_Lean_Meta_AbstractMVars_instMonadMCtxM);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
