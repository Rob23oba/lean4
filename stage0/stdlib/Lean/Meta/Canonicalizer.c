// Lean compiler output
// Module: Lean.Meta.Canonicalizer
// Imports: Lean.Util.ShareCommon Lean.Meta.Basic Lean.Meta.FunInfo Std.Data.HashMap.Raw
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
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_instHashableExprVisited___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Canonicalizer_canon_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4___redArg(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Canonicalizer_canon_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4(lean_object*, uint64_t, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__0(lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Canonicalizer_canon_spec__0___redArg(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Canonicalizer_canon_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_instBEqExprVisited___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_instInhabitedExprVisited;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon_unsafe__1(uint64_t, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Canonicalizer_canon_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_usize_to_uint64(size_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_instBEqExprVisited;
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_instInhabitedState;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Canonicalizer_canon_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_instHashableExprVisited;
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___redArg(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Meta_Canonicalizer_instHashableExprVisited___lam__0(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Canonicalizer_instBEqExprVisited___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___lam__0(lean_object*, uint64_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon_unsafe__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2(lean_object*, uint64_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___redArg(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Canonicalizer_canon_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1(lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1___redArg(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Canonicalizer_canon_spec__0(lean_object*, uint64_t, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isExplicit(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__0___redArg(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Canonicalizer_instInhabitedExprVisited() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(0);
x_4 = l_Lean_Expr_const___override(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Canonicalizer_instBEqExprVisited___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; uint8_t x_5; 
x_3 = lean_ptr_addr(x_1);
x_4 = lean_ptr_addr(x_2);
x_5 = lean_usize_dec_eq(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Canonicalizer_instBEqExprVisited() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Canonicalizer_instBEqExprVisited___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_instBEqExprVisited___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Canonicalizer_instBEqExprVisited___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Canonicalizer_instHashableExprVisited___lam__0(lean_object* x_1) {
_start:
{
size_t x_2; uint64_t x_3; 
x_2 = lean_ptr_addr(x_1);
x_3 = lean_usize_to_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Canonicalizer_instHashableExprVisited() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Canonicalizer_instHashableExprVisited___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_instHashableExprVisited___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Canonicalizer_instHashableExprVisited___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Canonicalizer_instInhabitedState() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_shiftl(x_1, x_3);
x_5 = lean_unsigned_to_nat(3u);
x_6 = lean_nat_div(x_4, x_5);
lean_dec(x_4);
x_7 = l_Nat_nextPowerOfTwo(x_6);
lean_dec(x_6);
x_8 = lean_box(0);
lean_inc(x_7);
x_9 = lean_mk_array(x_7, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_box(0);
x_12 = lean_mk_array(x_7, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_st_mk_ref(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(x_2);
lean_inc(x_10);
x_13 = lean_apply_7(x_1, x_12, x_10, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_10, x_15);
lean_dec(x_10);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_14);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_dec(x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Meta_Canonicalizer_CanonM_run_x27(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_mk_ref(x_3, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_box(x_2);
lean_inc(x_11);
x_14 = lean_apply_7(x_1, x_13, x_11, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_11, x_16);
lean_dec(x_11);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_9, 1, x_19);
lean_ctor_set(x_9, 0, x_15);
lean_ctor_set(x_17, 0, x_9);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_17);
lean_ctor_set(x_9, 1, x_20);
lean_ctor_set(x_9, 0, x_15);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_9);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_free_object(x_9);
lean_dec(x_11);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
return x_14;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_14);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_9, 0);
x_28 = lean_ctor_get(x_9, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_9);
x_29 = lean_box(x_2);
lean_inc(x_27);
x_30 = lean_apply_7(x_1, x_29, x_27, x_4, x_5, x_6, x_7, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_st_ref_get(x_27, x_32);
lean_dec(x_27);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_34);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_27);
x_39 = lean_ctor_get(x_30, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_30, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_41 = x_30;
} else {
 lean_dec_ref(x_30);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Canonicalizer_CanonM_run___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_Canonicalizer_CanonM_run___redArg(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Meta_Canonicalizer_CanonM_run(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ptr_addr(x_4);
x_8 = lean_ptr_addr(x_1);
x_9 = lean_usize_dec_eq(x_7, x_8);
if (x_9 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_11; 
lean_inc(x_5);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; size_t x_11; uint64_t x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; lean_object* x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; size_t x_21; size_t x_22; lean_object* x_23; size_t x_24; size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; 
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_array_get_size(x_9);
x_11 = lean_ptr_addr(x_1);
x_12 = lean_usize_to_uint64(x_11);
x_13 = lean_unsigned_to_nat(32u);
x_14 = lean_uint64_of_nat(x_13);
x_15 = lean_uint64_shift_right(x_12, x_14);
x_16 = lean_uint64_xor(x_12, x_15);
x_17 = lean_unsigned_to_nat(16u);
x_18 = lean_uint64_of_nat(x_17);
x_19 = lean_uint64_shift_right(x_16, x_18);
x_20 = lean_uint64_xor(x_16, x_19);
x_21 = lean_uint64_to_usize(x_20);
x_22 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_usize_of_nat(x_23);
x_25 = lean_usize_sub(x_22, x_24);
x_26 = lean_usize_land(x_21, x_25);
x_27 = lean_array_uget(x_9, x_26);
x_28 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___redArg(x_1, x_27);
lean_dec(x_27);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ptr_addr(x_5);
x_8 = lean_ptr_addr(x_1);
x_9 = lean_usize_dec_eq(x_7, x_8);
if (x_9 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
return x_9;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; uint64_t x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; size_t x_17; size_t x_18; lean_object* x_19; size_t x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = lean_ptr_addr(x_4);
x_8 = lean_usize_to_uint64(x_7);
x_9 = lean_unsigned_to_nat(32u);
x_10 = lean_uint64_of_nat(x_9);
x_11 = lean_uint64_shift_right(x_8, x_10);
x_12 = lean_uint64_xor(x_8, x_11);
x_13 = lean_unsigned_to_nat(16u);
x_14 = lean_uint64_of_nat(x_13);
x_15 = lean_uint64_shift_right(x_12, x_14);
x_16 = lean_uint64_xor(x_12, x_15);
x_17 = lean_uint64_to_usize(x_16);
x_18 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_usize_of_nat(x_19);
x_21 = lean_usize_sub(x_18, x_20);
x_22 = lean_usize_land(x_17, x_21);
x_23 = lean_array_uget(x_1, x_22);
lean_ctor_set(x_2, 2, x_23);
x_24 = lean_array_uset(x_1, x_22, x_2);
x_1 = x_24;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; uint64_t x_31; lean_object* x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; lean_object* x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; size_t x_40; size_t x_41; lean_object* x_42; size_t x_43; size_t x_44; size_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_2, 1);
x_28 = lean_ctor_get(x_2, 2);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_2);
x_29 = lean_array_get_size(x_1);
x_30 = lean_ptr_addr(x_26);
x_31 = lean_usize_to_uint64(x_30);
x_32 = lean_unsigned_to_nat(32u);
x_33 = lean_uint64_of_nat(x_32);
x_34 = lean_uint64_shift_right(x_31, x_33);
x_35 = lean_uint64_xor(x_31, x_34);
x_36 = lean_unsigned_to_nat(16u);
x_37 = lean_uint64_of_nat(x_36);
x_38 = lean_uint64_shift_right(x_35, x_37);
x_39 = lean_uint64_xor(x_35, x_38);
x_40 = lean_uint64_to_usize(x_39);
x_41 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_usize_of_nat(x_42);
x_44 = lean_usize_sub(x_41, x_43);
x_45 = lean_usize_land(x_40, x_44);
x_46 = lean_array_uget(x_1, x_45);
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_26);
lean_ctor_set(x_47, 1, x_27);
lean_ctor_set(x_47, 2, x_46);
x_48 = lean_array_uset(x_1, x_45, x_47);
x_1 = x_48;
x_2 = x_28;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__1_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__1_spec__1_spec__1___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__1___redArg(lean_object* x_1) {
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
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__1_spec__1___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_ptr_addr(x_5);
x_9 = lean_ptr_addr(x_1);
x_10 = lean_usize_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__4___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_11);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get(x_3, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_15 = lean_ptr_addr(x_12);
x_16 = lean_ptr_addr(x_1);
x_17 = lean_usize_dec_eq(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__4___redArg(x_1, x_2, x_14);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
return x_19;
}
else
{
lean_object* x_20; 
lean_dec(x_13);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_2);
lean_ctor_set(x_20, 2, x_14);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__4___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___redArg(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_10 = x_6;
} else {
 lean_dec_ref(x_6);
 x_10 = lean_box(0);
}
x_11 = lean_box(0);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
x_22 = lean_array_get_size(x_21);
lean_dec(x_21);
x_23 = lean_nat_dec_lt(x_20, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_dec(x_1);
x_12 = x_8;
goto block_19;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_8);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; uint64_t x_29; lean_object* x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; lean_object* x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; size_t x_38; size_t x_39; lean_object* x_40; size_t x_41; size_t x_42; size_t x_43; lean_object* x_44; uint8_t x_45; 
x_25 = lean_ctor_get(x_8, 0);
x_26 = lean_ctor_get(x_8, 1);
x_27 = lean_array_get_size(x_26);
x_28 = lean_ptr_addr(x_1);
x_29 = lean_usize_to_uint64(x_28);
x_30 = lean_unsigned_to_nat(32u);
x_31 = lean_uint64_of_nat(x_30);
x_32 = lean_uint64_shift_right(x_29, x_31);
x_33 = lean_uint64_xor(x_29, x_32);
x_34 = lean_unsigned_to_nat(16u);
x_35 = lean_uint64_of_nat(x_34);
x_36 = lean_uint64_shift_right(x_33, x_35);
x_37 = lean_uint64_xor(x_33, x_36);
x_38 = lean_uint64_to_usize(x_37);
x_39 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_usize_of_nat(x_40);
x_42 = lean_usize_sub(x_39, x_41);
x_43 = lean_usize_land(x_38, x_42);
x_44 = lean_array_uget(x_26, x_43);
x_45 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__0___redArg(x_1, x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_46 = lean_nat_add(x_25, x_40);
lean_dec(x_25);
x_47 = lean_box_uint64(x_2);
x_48 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 2, x_44);
x_49 = lean_array_uset(x_26, x_43, x_48);
x_50 = lean_unsigned_to_nat(2u);
x_51 = lean_nat_shiftl(x_46, x_50);
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
x_56 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__1___redArg(x_49);
lean_ctor_set(x_8, 1, x_56);
lean_ctor_set(x_8, 0, x_46);
x_12 = x_8;
goto block_19;
}
else
{
lean_ctor_set(x_8, 1, x_49);
lean_ctor_set(x_8, 0, x_46);
x_12 = x_8;
goto block_19;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_box(0);
x_58 = lean_array_uset(x_26, x_43, x_57);
x_59 = lean_box_uint64(x_2);
x_60 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__4___redArg(x_1, x_59, x_44);
x_61 = lean_array_uset(x_58, x_43, x_60);
lean_ctor_set(x_8, 1, x_61);
x_12 = x_8;
goto block_19;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; size_t x_65; uint64_t x_66; lean_object* x_67; uint64_t x_68; uint64_t x_69; uint64_t x_70; lean_object* x_71; uint64_t x_72; uint64_t x_73; uint64_t x_74; size_t x_75; size_t x_76; lean_object* x_77; size_t x_78; size_t x_79; size_t x_80; lean_object* x_81; uint8_t x_82; 
x_62 = lean_ctor_get(x_8, 0);
x_63 = lean_ctor_get(x_8, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_8);
x_64 = lean_array_get_size(x_63);
x_65 = lean_ptr_addr(x_1);
x_66 = lean_usize_to_uint64(x_65);
x_67 = lean_unsigned_to_nat(32u);
x_68 = lean_uint64_of_nat(x_67);
x_69 = lean_uint64_shift_right(x_66, x_68);
x_70 = lean_uint64_xor(x_66, x_69);
x_71 = lean_unsigned_to_nat(16u);
x_72 = lean_uint64_of_nat(x_71);
x_73 = lean_uint64_shift_right(x_70, x_72);
x_74 = lean_uint64_xor(x_70, x_73);
x_75 = lean_uint64_to_usize(x_74);
x_76 = lean_usize_of_nat(x_64);
lean_dec(x_64);
x_77 = lean_unsigned_to_nat(1u);
x_78 = lean_usize_of_nat(x_77);
x_79 = lean_usize_sub(x_76, x_78);
x_80 = lean_usize_land(x_75, x_79);
x_81 = lean_array_uget(x_63, x_80);
x_82 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__0___redArg(x_1, x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_83 = lean_nat_add(x_62, x_77);
lean_dec(x_62);
x_84 = lean_box_uint64(x_2);
x_85 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_85, 0, x_1);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set(x_85, 2, x_81);
x_86 = lean_array_uset(x_63, x_80, x_85);
x_87 = lean_unsigned_to_nat(2u);
x_88 = lean_nat_shiftl(x_83, x_87);
x_89 = lean_unsigned_to_nat(3u);
x_90 = lean_nat_div(x_88, x_89);
lean_dec(x_88);
x_91 = lean_array_get_size(x_86);
x_92 = lean_nat_dec_le(x_90, x_91);
lean_dec(x_91);
lean_dec(x_90);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__1___redArg(x_86);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_83);
lean_ctor_set(x_94, 1, x_93);
x_12 = x_94;
goto block_19;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_83);
lean_ctor_set(x_95, 1, x_86);
x_12 = x_95;
goto block_19;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_96 = lean_box(0);
x_97 = lean_array_uset(x_63, x_80, x_96);
x_98 = lean_box_uint64(x_2);
x_99 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__4___redArg(x_1, x_98, x_81);
x_100 = lean_array_uset(x_97, x_80, x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_62);
lean_ctor_set(x_101, 1, x_100);
x_12 = x_101;
goto block_19;
}
}
}
block_19:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
if (lean_is_scalar(x_10)) {
 x_13 = lean_alloc_ctor(0, 2, 0);
} else {
 x_13 = x_10;
}
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
x_14 = lean_st_ref_set(x_3, x_13, x_7);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_11);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2(lean_object* x_1, uint64_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___redArg(x_1, x_2, x_4, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_6 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___redArg(x_1, x_5, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint64_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(x_1, x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint64_t x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint64_t x_13; lean_object* x_14; lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_3, 1);
x_20 = lean_nat_dec_lt(x_5, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_21 = lean_box_uint64(x_4);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_12);
return x_22;
}
else
{
lean_object* x_23; uint8_t x_24; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_23 = l_Lean_Expr_getAppNumArgs(x_1);
x_35 = lean_ctor_get(x_2, 0);
x_36 = lean_array_get_size(x_35);
x_37 = lean_nat_dec_lt(x_5, x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_nat_sub(x_23, x_5);
lean_dec(x_23);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_sub(x_38, x_39);
lean_dec(x_38);
x_41 = l_Lean_Expr_getRevArg_x21(x_1, x_40);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_42 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_41, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; uint64_t x_45; uint64_t x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_unbox_uint64(x_43);
lean_dec(x_43);
x_46 = lean_uint64_mix_hash(x_4, x_45);
x_13 = x_46;
x_14 = x_44;
goto block_18;
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
return x_42;
}
}
else
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_array_fget(x_35, x_5);
x_48 = l_Lean_Meta_ParamInfo_isExplicit(x_47);
if (x_48 == 0)
{
lean_dec(x_47);
x_24 = x_48;
goto block_34;
}
else
{
uint8_t x_49; 
x_49 = lean_ctor_get_uint8(x_47, sizeof(void*)*1 + 2);
lean_dec(x_47);
if (x_49 == 0)
{
x_24 = x_48;
goto block_34;
}
else
{
lean_dec(x_23);
x_13 = x_4;
x_14 = x_12;
goto block_18;
}
}
}
block_34:
{
if (x_24 == 0)
{
lean_dec(x_23);
x_13 = x_4;
x_14 = x_12;
goto block_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_nat_sub(x_23, x_5);
lean_dec(x_23);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_sub(x_25, x_26);
lean_dec(x_25);
x_28 = l_Lean_Expr_getRevArg_x21(x_1, x_27);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_29 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; uint64_t x_32; uint64_t x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_unbox_uint64(x_30);
lean_dec(x_30);
x_33 = lean_uint64_mix_hash(x_4, x_32);
x_13 = x_33;
x_14 = x_31;
goto block_18;
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
return x_29;
}
}
}
}
block_18:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_3, 2);
x_16 = lean_nat_add(x_5, x_15);
lean_dec(x_5);
x_4 = x_13;
x_5 = x_16;
x_12 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint64_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___lam__0(lean_object* x_1, uint64_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___redArg(x_1, x_2, x_4, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
x_13 = lean_box_uint64(x_2);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_box_uint64(x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_unbox_uint64(x_13);
lean_dec(x_13);
x_19 = lean_unbox_uint64(x_17);
lean_dec(x_17);
x_20 = lean_uint64_mix_hash(x_18, x_19);
x_21 = lean_box_uint64(x_20);
lean_ctor_set(x_15, 0, x_21);
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_unbox_uint64(x_13);
lean_dec(x_13);
x_25 = lean_unbox_uint64(x_22);
lean_dec(x_22);
x_26 = lean_uint64_mix_hash(x_24, x_25);
x_27 = lean_box_uint64(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
return x_28;
}
}
else
{
lean_dec(x_13);
return x_15;
}
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1(x_1, x_11);
lean_dec(x_11);
if (lean_obj_tag(x_13) == 0)
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_14; uint8_t x_15; 
lean_free_object(x_9);
lean_inc(x_1);
x_14 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(x_1, x_5, x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_expr_eqv(x_16, x_1);
if (x_18 == 0)
{
lean_object* x_19; 
lean_free_object(x_14);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_19 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint64_t x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unbox_uint64(x_20);
lean_dec(x_20);
x_23 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___lam__0(x_1, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_23;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_19;
}
}
else
{
uint64_t x_24; lean_object* x_25; 
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_24 = l_Lean_Expr_hash(x_1);
lean_dec(x_1);
x_25 = lean_box_uint64(x_24);
lean_ctor_set(x_14, 0, x_25);
return x_14;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
x_28 = lean_expr_eqv(x_26, x_1);
if (x_28 == 0)
{
lean_object* x_29; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_29 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; uint64_t x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_unbox_uint64(x_30);
lean_dec(x_30);
x_33 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___lam__0(x_1, x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_31);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_33;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_29;
}
}
else
{
uint64_t x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_34 = l_Lean_Expr_hash(x_1);
lean_dec(x_1);
x_35 = lean_box_uint64(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_27);
return x_36;
}
}
}
case 4:
{
lean_object* x_37; uint64_t x_38; lean_object* x_39; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
lean_dec(x_1);
x_38 = l_Lean_Name_hash___override(x_37);
lean_dec(x_37);
x_39 = lean_box_uint64(x_38);
lean_ctor_set(x_9, 0, x_39);
return x_9;
}
case 5:
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_78; 
lean_free_object(x_9);
x_40 = l_Lean_Expr_getAppFn(x_1);
x_78 = l_Lean_Expr_isMVar(x_40);
if (x_78 == 0)
{
x_59 = x_2;
x_60 = x_3;
x_61 = x_4;
x_62 = x_5;
x_63 = x_6;
x_64 = x_7;
x_65 = x_12;
goto block_77;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
lean_inc(x_1);
x_79 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(x_1, x_5, x_12);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_expr_eqv(x_80, x_1);
if (x_82 == 0)
{
lean_dec(x_40);
lean_dec(x_1);
x_1 = x_80;
x_8 = x_81;
goto _start;
}
else
{
lean_dec(x_80);
x_59 = x_2;
x_60 = x_3;
x_61 = x_4;
x_62 = x_5;
x_63 = x_6;
x_64 = x_7;
x_65 = x_81;
goto block_77;
}
}
block_58:
{
lean_object* x_49; 
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
x_49 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_40, x_42, x_43, x_44, x_45, x_46, x_47, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint64_t x_56; lean_object* x_57; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_unsigned_to_nat(0u);
x_53 = l_Lean_Expr_getAppNumArgs(x_1);
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_53);
lean_ctor_set(x_55, 2, x_54);
x_56 = lean_unbox_uint64(x_50);
lean_dec(x_50);
x_57 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(x_1, x_41, x_55, x_56, x_52, x_42, x_43, x_44, x_45, x_46, x_47, x_51);
lean_dec(x_55);
lean_dec(x_41);
lean_dec(x_1);
return x_57;
}
else
{
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_1);
return x_49;
}
}
block_77:
{
uint8_t x_66; 
x_66 = l_Lean_Expr_hasLooseBVars(x_40);
if (x_66 == 0)
{
lean_object* x_67; 
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_40);
x_67 = l_Lean_Meta_getFunInfo(x_40, x_61, x_62, x_63, x_64, x_65);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_41 = x_68;
x_42 = x_59;
x_43 = x_60;
x_44 = x_61;
x_45 = x_62;
x_46 = x_63;
x_47 = x_64;
x_48 = x_69;
goto block_58;
}
else
{
uint8_t x_70; 
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_40);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_67);
if (x_70 == 0)
{
return x_67;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_67, 0);
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_67);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_mk_empty_array_with_capacity(x_74);
lean_inc(x_75);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_75);
x_41 = x_76;
x_42 = x_59;
x_43 = x_60;
x_44 = x_61;
x_45 = x_62;
x_46 = x_63;
x_47 = x_64;
x_48 = x_65;
goto block_58;
}
}
}
case 6:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; 
lean_free_object(x_9);
x_84 = lean_ctor_get(x_1, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_1, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_1, 2);
lean_inc(x_86);
x_87 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_88 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___lam__1(x_84, x_85, x_86, x_87, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
lean_dec(x_84);
return x_88;
}
case 7:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; 
lean_free_object(x_9);
x_89 = lean_ctor_get(x_1, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_1, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_1, 2);
lean_inc(x_91);
x_92 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_93 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___lam__1(x_89, x_90, x_91, x_92, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
lean_dec(x_89);
return x_93;
}
case 8:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_free_object(x_9);
x_94 = lean_ctor_get(x_1, 2);
lean_inc(x_94);
x_95 = lean_ctor_get(x_1, 3);
lean_inc(x_95);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_96 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_94, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_95, x_2, x_3, x_4, x_5, x_6, x_7, x_98);
if (lean_obj_tag(x_99) == 0)
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; uint64_t x_102; uint64_t x_103; uint64_t x_104; lean_object* x_105; 
x_101 = lean_ctor_get(x_99, 0);
x_102 = lean_unbox_uint64(x_97);
lean_dec(x_97);
x_103 = lean_unbox_uint64(x_101);
lean_dec(x_101);
x_104 = lean_uint64_mix_hash(x_102, x_103);
x_105 = lean_box_uint64(x_104);
lean_ctor_set(x_99, 0, x_105);
return x_99;
}
else
{
lean_object* x_106; lean_object* x_107; uint64_t x_108; uint64_t x_109; uint64_t x_110; lean_object* x_111; lean_object* x_112; 
x_106 = lean_ctor_get(x_99, 0);
x_107 = lean_ctor_get(x_99, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_99);
x_108 = lean_unbox_uint64(x_97);
lean_dec(x_97);
x_109 = lean_unbox_uint64(x_106);
lean_dec(x_106);
x_110 = lean_uint64_mix_hash(x_108, x_109);
x_111 = lean_box_uint64(x_110);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_107);
return x_112;
}
}
else
{
lean_dec(x_97);
return x_99;
}
}
else
{
lean_dec(x_95);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_96;
}
}
case 10:
{
lean_object* x_113; lean_object* x_114; 
lean_free_object(x_9);
x_113 = lean_ctor_get(x_1, 1);
lean_inc(x_113);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_114 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_113, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; uint64_t x_117; lean_object* x_118; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = lean_unbox_uint64(x_115);
lean_dec(x_115);
x_118 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___lam__0(x_1, x_117, x_2, x_3, x_4, x_5, x_6, x_7, x_116);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_118;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_114;
}
}
case 11:
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_free_object(x_9);
x_119 = lean_ctor_get(x_1, 1);
lean_inc(x_119);
x_120 = lean_ctor_get(x_1, 2);
lean_inc(x_120);
lean_dec(x_1);
x_121 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_120, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_121) == 0)
{
uint8_t x_122; 
x_122 = !lean_is_exclusive(x_121);
if (x_122 == 0)
{
lean_object* x_123; uint64_t x_124; uint64_t x_125; uint64_t x_126; lean_object* x_127; 
x_123 = lean_ctor_get(x_121, 0);
x_124 = lean_uint64_of_nat(x_119);
lean_dec(x_119);
x_125 = lean_unbox_uint64(x_123);
lean_dec(x_123);
x_126 = lean_uint64_mix_hash(x_124, x_125);
x_127 = lean_box_uint64(x_126);
lean_ctor_set(x_121, 0, x_127);
return x_121;
}
else
{
lean_object* x_128; lean_object* x_129; uint64_t x_130; uint64_t x_131; uint64_t x_132; lean_object* x_133; lean_object* x_134; 
x_128 = lean_ctor_get(x_121, 0);
x_129 = lean_ctor_get(x_121, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_121);
x_130 = lean_uint64_of_nat(x_119);
lean_dec(x_119);
x_131 = lean_unbox_uint64(x_128);
lean_dec(x_128);
x_132 = lean_uint64_mix_hash(x_130, x_131);
x_133 = lean_box_uint64(x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_129);
return x_134;
}
}
else
{
lean_dec(x_119);
return x_121;
}
}
default: 
{
uint64_t x_135; lean_object* x_136; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_135 = l_Lean_Expr_hash(x_1);
lean_dec(x_1);
x_136 = lean_box_uint64(x_135);
lean_ctor_set(x_9, 0, x_136);
return x_9;
}
}
}
else
{
lean_object* x_137; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_137 = lean_ctor_get(x_13, 0);
lean_inc(x_137);
lean_dec(x_13);
lean_ctor_set(x_9, 0, x_137);
return x_9;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_9, 0);
x_139 = lean_ctor_get(x_9, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_9);
x_140 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1(x_1, x_138);
lean_dec(x_138);
if (lean_obj_tag(x_140) == 0)
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
lean_inc(x_1);
x_141 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(x_1, x_5, x_139);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_144 = x_141;
} else {
 lean_dec_ref(x_141);
 x_144 = lean_box(0);
}
x_145 = lean_expr_eqv(x_142, x_1);
if (x_145 == 0)
{
lean_object* x_146; 
lean_dec(x_144);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_146 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_142, x_2, x_3, x_4, x_5, x_6, x_7, x_143);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; uint64_t x_149; lean_object* x_150; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_unbox_uint64(x_147);
lean_dec(x_147);
x_150 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___lam__0(x_1, x_149, x_2, x_3, x_4, x_5, x_6, x_7, x_148);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_150;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_146;
}
}
else
{
uint64_t x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_142);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_151 = l_Lean_Expr_hash(x_1);
lean_dec(x_1);
x_152 = lean_box_uint64(x_151);
if (lean_is_scalar(x_144)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_144;
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_143);
return x_153;
}
}
case 4:
{
lean_object* x_154; uint64_t x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_154 = lean_ctor_get(x_1, 0);
lean_inc(x_154);
lean_dec(x_1);
x_155 = l_Lean_Name_hash___override(x_154);
lean_dec(x_154);
x_156 = lean_box_uint64(x_155);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_139);
return x_157;
}
case 5:
{
lean_object* x_158; lean_object* x_159; uint8_t x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_196; 
x_158 = l_Lean_Expr_getAppFn(x_1);
x_196 = l_Lean_Expr_isMVar(x_158);
if (x_196 == 0)
{
x_177 = x_2;
x_178 = x_3;
x_179 = x_4;
x_180 = x_5;
x_181 = x_6;
x_182 = x_7;
x_183 = x_139;
goto block_195;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
lean_inc(x_1);
x_197 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(x_1, x_5, x_139);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
lean_dec(x_197);
x_200 = lean_expr_eqv(x_198, x_1);
if (x_200 == 0)
{
lean_dec(x_158);
lean_dec(x_1);
x_1 = x_198;
x_8 = x_199;
goto _start;
}
else
{
lean_dec(x_198);
x_177 = x_2;
x_178 = x_3;
x_179 = x_4;
x_180 = x_5;
x_181 = x_6;
x_182 = x_7;
x_183 = x_199;
goto block_195;
}
}
block_176:
{
lean_object* x_167; 
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
x_167 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_158, x_160, x_161, x_162, x_163, x_164, x_165, x_166);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint64_t x_174; lean_object* x_175; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_unsigned_to_nat(0u);
x_171 = l_Lean_Expr_getAppNumArgs(x_1);
x_172 = lean_unsigned_to_nat(1u);
x_173 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
lean_ctor_set(x_173, 2, x_172);
x_174 = lean_unbox_uint64(x_168);
lean_dec(x_168);
x_175 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(x_1, x_159, x_173, x_174, x_170, x_160, x_161, x_162, x_163, x_164, x_165, x_169);
lean_dec(x_173);
lean_dec(x_159);
lean_dec(x_1);
return x_175;
}
else
{
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_159);
lean_dec(x_1);
return x_167;
}
}
block_195:
{
uint8_t x_184; 
x_184 = l_Lean_Expr_hasLooseBVars(x_158);
if (x_184 == 0)
{
lean_object* x_185; 
lean_inc(x_182);
lean_inc(x_181);
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_158);
x_185 = l_Lean_Meta_getFunInfo(x_158, x_179, x_180, x_181, x_182, x_183);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_159 = x_186;
x_160 = x_177;
x_161 = x_178;
x_162 = x_179;
x_163 = x_180;
x_164 = x_181;
x_165 = x_182;
x_166 = x_187;
goto block_176;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_158);
lean_dec(x_1);
x_188 = lean_ctor_get(x_185, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_185, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_190 = x_185;
} else {
 lean_dec_ref(x_185);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_unsigned_to_nat(0u);
x_193 = lean_mk_empty_array_with_capacity(x_192);
lean_inc(x_193);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_193);
x_159 = x_194;
x_160 = x_177;
x_161 = x_178;
x_162 = x_179;
x_163 = x_180;
x_164 = x_181;
x_165 = x_182;
x_166 = x_183;
goto block_176;
}
}
}
case 6:
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; 
x_202 = lean_ctor_get(x_1, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_1, 1);
lean_inc(x_203);
x_204 = lean_ctor_get(x_1, 2);
lean_inc(x_204);
x_205 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_206 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___lam__1(x_202, x_203, x_204, x_205, x_2, x_3, x_4, x_5, x_6, x_7, x_139);
lean_dec(x_202);
return x_206;
}
case 7:
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; lean_object* x_211; 
x_207 = lean_ctor_get(x_1, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_1, 1);
lean_inc(x_208);
x_209 = lean_ctor_get(x_1, 2);
lean_inc(x_209);
x_210 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_211 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___lam__1(x_207, x_208, x_209, x_210, x_2, x_3, x_4, x_5, x_6, x_7, x_139);
lean_dec(x_207);
return x_211;
}
case 8:
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_1, 2);
lean_inc(x_212);
x_213 = lean_ctor_get(x_1, 3);
lean_inc(x_213);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_214 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_212, x_2, x_3, x_4, x_5, x_6, x_7, x_139);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_217 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_213, x_2, x_3, x_4, x_5, x_6, x_7, x_216);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; uint64_t x_221; uint64_t x_222; uint64_t x_223; lean_object* x_224; lean_object* x_225; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_220 = x_217;
} else {
 lean_dec_ref(x_217);
 x_220 = lean_box(0);
}
x_221 = lean_unbox_uint64(x_215);
lean_dec(x_215);
x_222 = lean_unbox_uint64(x_218);
lean_dec(x_218);
x_223 = lean_uint64_mix_hash(x_221, x_222);
x_224 = lean_box_uint64(x_223);
if (lean_is_scalar(x_220)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_220;
}
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_219);
return x_225;
}
else
{
lean_dec(x_215);
return x_217;
}
}
else
{
lean_dec(x_213);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_214;
}
}
case 10:
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_ctor_get(x_1, 1);
lean_inc(x_226);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_227 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_226, x_2, x_3, x_4, x_5, x_6, x_7, x_139);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; uint64_t x_230; lean_object* x_231; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
x_230 = lean_unbox_uint64(x_228);
lean_dec(x_228);
x_231 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___lam__0(x_1, x_230, x_2, x_3, x_4, x_5, x_6, x_7, x_229);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_231;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_227;
}
}
case 11:
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_1, 1);
lean_inc(x_232);
x_233 = lean_ctor_get(x_1, 2);
lean_inc(x_233);
lean_dec(x_1);
x_234 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_233, x_2, x_3, x_4, x_5, x_6, x_7, x_139);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; uint64_t x_238; uint64_t x_239; uint64_t x_240; lean_object* x_241; lean_object* x_242; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_237 = x_234;
} else {
 lean_dec_ref(x_234);
 x_237 = lean_box(0);
}
x_238 = lean_uint64_of_nat(x_232);
lean_dec(x_232);
x_239 = lean_unbox_uint64(x_235);
lean_dec(x_235);
x_240 = lean_uint64_mix_hash(x_238, x_239);
x_241 = lean_box_uint64(x_240);
if (lean_is_scalar(x_237)) {
 x_242 = lean_alloc_ctor(0, 2, 0);
} else {
 x_242 = x_237;
}
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_236);
return x_242;
}
else
{
lean_dec(x_232);
return x_234;
}
}
default: 
{
uint64_t x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_243 = l_Lean_Expr_hash(x_1);
lean_dec(x_1);
x_244 = lean_box_uint64(x_243);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_139);
return x_245;
}
}
}
else
{
lean_object* x_246; lean_object* x_247; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_246 = lean_ctor_get(x_140, 0);
lean_inc(x_246);
lean_dec(x_140);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_139);
return x_247;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint64_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_14 = lean_unbox(x_6);
lean_dec(x_6);
x_15 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(x_1, x_2, x_3, x_13, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint64_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_16 = lean_unbox(x_8);
lean_dec(x_8);
x_17 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_16, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint64_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___lam__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___lam__1(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___redArg(uint64_t x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_8 = lean_uint64_dec_eq(x_7, x_1);
if (x_8 == 0)
{
lean_dec(x_5);
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_10; 
lean_dec(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_5);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon_unsafe__1(uint64_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; lean_object* x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_3, 1);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(32u);
x_7 = lean_uint64_of_nat(x_6);
x_8 = lean_uint64_shift_right(x_1, x_7);
x_9 = lean_uint64_xor(x_1, x_8);
x_10 = lean_unsigned_to_nat(16u);
x_11 = lean_uint64_of_nat(x_10);
x_12 = lean_uint64_shift_right(x_9, x_11);
x_13 = lean_uint64_xor(x_9, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_sub(x_15, x_17);
x_19 = lean_usize_land(x_14, x_18);
x_20 = lean_array_uget(x_4, x_19);
x_21 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___redArg(x_1, x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___redArg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon_unsafe__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_Lean_Meta_Canonicalizer_canon_unsafe__1(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Canonicalizer_canon_spec__0___redArg(uint64_t x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; uint64_t x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_unbox_uint64(x_5);
lean_dec(x_5);
x_8 = lean_uint64_dec_eq(x_7, x_1);
if (x_8 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_dec(x_6);
return x_8;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Canonicalizer_canon_spec__0(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Canonicalizer_canon_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; size_t x_17; size_t x_18; lean_object* x_19; size_t x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = lean_unsigned_to_nat(32u);
x_8 = lean_uint64_of_nat(x_7);
x_9 = lean_unbox_uint64(x_4);
x_10 = lean_uint64_shift_right(x_9, x_8);
x_11 = lean_unbox_uint64(x_4);
x_12 = lean_uint64_xor(x_11, x_10);
x_13 = lean_unsigned_to_nat(16u);
x_14 = lean_uint64_of_nat(x_13);
x_15 = lean_uint64_shift_right(x_12, x_14);
x_16 = lean_uint64_xor(x_12, x_15);
x_17 = lean_uint64_to_usize(x_16);
x_18 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_usize_of_nat(x_19);
x_21 = lean_usize_sub(x_18, x_20);
x_22 = lean_usize_land(x_17, x_21);
x_23 = lean_array_uget(x_1, x_22);
lean_ctor_set(x_2, 2, x_23);
x_24 = lean_array_uset(x_1, x_22, x_2);
x_1 = x_24;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; lean_object* x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; size_t x_40; size_t x_41; lean_object* x_42; size_t x_43; size_t x_44; size_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_2, 1);
x_28 = lean_ctor_get(x_2, 2);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_2);
x_29 = lean_array_get_size(x_1);
x_30 = lean_unsigned_to_nat(32u);
x_31 = lean_uint64_of_nat(x_30);
x_32 = lean_unbox_uint64(x_26);
x_33 = lean_uint64_shift_right(x_32, x_31);
x_34 = lean_unbox_uint64(x_26);
x_35 = lean_uint64_xor(x_34, x_33);
x_36 = lean_unsigned_to_nat(16u);
x_37 = lean_uint64_of_nat(x_36);
x_38 = lean_uint64_shift_right(x_35, x_37);
x_39 = lean_uint64_xor(x_35, x_38);
x_40 = lean_uint64_to_usize(x_39);
x_41 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_usize_of_nat(x_42);
x_44 = lean_usize_sub(x_41, x_43);
x_45 = lean_usize_land(x_40, x_44);
x_46 = lean_array_uget(x_1, x_45);
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_26);
lean_ctor_set(x_47, 1, x_27);
lean_ctor_set(x_47, 2, x_46);
x_48 = lean_array_uset(x_1, x_45, x_47);
x_1 = x_48;
x_2 = x_28;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1_spec__1_spec__1___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1___redArg(lean_object* x_1) {
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
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1_spec__1___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4___redArg(uint64_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_unbox_uint64(x_5);
x_9 = lean_uint64_dec_eq(x_8, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_10);
return x_3;
}
else
{
lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
x_11 = lean_box_uint64(x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_11);
return x_3;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint64_t x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get(x_3, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_15 = lean_unbox_uint64(x_12);
x_16 = lean_uint64_dec_eq(x_15, x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4___redArg(x_1, x_2, x_14);
x_18 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
lean_dec(x_12);
x_19 = lean_box_uint64(x_1);
x_20 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_2);
lean_ctor_set(x_20, 2, x_14);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Canonicalizer_canon_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_3);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_11);
lean_inc(x_1);
x_13 = l_Lean_Meta_isExprDefEq(x_1, x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_box(0);
x_18 = lean_unbox(x_15);
lean_dec(x_15);
if (x_18 == 0)
{
lean_object* x_19; 
lean_free_object(x_13);
lean_dec(x_11);
x_19 = lean_box(0);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_17);
lean_ctor_set(x_2, 0, x_19);
{
lean_object* _tmp_1 = x_12;
lean_object* _tmp_2 = x_2;
lean_object* _tmp_7 = x_16;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_8 = _tmp_7;
}
goto _start;
}
else
{
lean_object* x_21; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_17);
lean_ctor_set(x_2, 0, x_21);
lean_ctor_set(x_13, 0, x_2);
return x_13;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_box(0);
x_25 = lean_unbox(x_22);
lean_dec(x_22);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_11);
x_26 = lean_box(0);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_24);
lean_ctor_set(x_2, 0, x_26);
{
lean_object* _tmp_1 = x_12;
lean_object* _tmp_2 = x_2;
lean_object* _tmp_7 = x_23;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_8 = _tmp_7;
}
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_11);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_24);
lean_ctor_set(x_2, 0, x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_23);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_free_object(x_2);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_13);
if (x_30 == 0)
{
return x_13;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_13, 0);
x_32 = lean_ctor_get(x_13, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_13);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_2, 0);
x_35 = lean_ctor_get(x_2, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_34);
lean_inc(x_1);
x_36 = l_Lean_Meta_isExprDefEq(x_1, x_34, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
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
x_40 = lean_box(0);
x_41 = lean_unbox(x_37);
lean_dec(x_37);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_39);
lean_dec(x_34);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
x_2 = x_35;
x_3 = x_43;
x_8 = x_38;
goto _start;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_35);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_34);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_40);
if (lean_is_scalar(x_39)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_39;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_38);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_48 = lean_ctor_get(x_36, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_36, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_50 = x_36;
} else {
 lean_dec_ref(x_36);
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
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Canonicalizer_canon_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at___Lean_Meta_Canonicalizer_canon_spec__5___redArg(x_1, x_3, x_4, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_9 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_3, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint64_t x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_unbox_uint64(x_10);
x_17 = l_Lean_Meta_Canonicalizer_canon_unsafe__1(x_16, x_14);
lean_dec(x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
lean_free_object(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_18 = lean_st_ref_take(x_3, x_15);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_33; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_24 = x_20;
} else {
 lean_dec_ref(x_20);
 x_24 = lean_box(0);
}
x_33 = !lean_is_exclusive(x_23);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; lean_object* x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; size_t x_48; size_t x_49; lean_object* x_50; size_t x_51; size_t x_52; size_t x_53; lean_object* x_54; uint64_t x_55; uint8_t x_56; 
x_34 = lean_ctor_get(x_23, 0);
x_35 = lean_ctor_get(x_23, 1);
x_36 = lean_box(0);
lean_inc(x_1);
lean_ctor_set_tag(x_18, 1);
lean_ctor_set(x_18, 1, x_36);
lean_ctor_set(x_18, 0, x_1);
x_37 = lean_array_get_size(x_35);
x_38 = lean_unsigned_to_nat(32u);
x_39 = lean_uint64_of_nat(x_38);
x_40 = lean_unbox_uint64(x_10);
x_41 = lean_uint64_shift_right(x_40, x_39);
x_42 = lean_unbox_uint64(x_10);
x_43 = lean_uint64_xor(x_42, x_41);
x_44 = lean_unsigned_to_nat(16u);
x_45 = lean_uint64_of_nat(x_44);
x_46 = lean_uint64_shift_right(x_43, x_45);
x_47 = lean_uint64_xor(x_43, x_46);
x_48 = lean_uint64_to_usize(x_47);
x_49 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_usize_of_nat(x_50);
x_52 = lean_usize_sub(x_49, x_51);
x_53 = lean_usize_land(x_48, x_52);
x_54 = lean_array_uget(x_35, x_53);
x_55 = lean_unbox_uint64(x_10);
lean_inc(x_54);
x_56 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Canonicalizer_canon_spec__0___redArg(x_55, x_54);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_57 = lean_nat_add(x_34, x_50);
lean_dec(x_34);
x_58 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_58, 0, x_10);
lean_ctor_set(x_58, 1, x_18);
lean_ctor_set(x_58, 2, x_54);
x_59 = lean_array_uset(x_35, x_53, x_58);
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
lean_object* x_66; 
x_66 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1___redArg(x_59);
lean_ctor_set(x_23, 1, x_66);
lean_ctor_set(x_23, 0, x_57);
x_25 = x_23;
goto block_32;
}
else
{
lean_ctor_set(x_23, 1, x_59);
lean_ctor_set(x_23, 0, x_57);
x_25 = x_23;
goto block_32;
}
}
else
{
lean_object* x_67; lean_object* x_68; uint64_t x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_box(0);
x_68 = lean_array_uset(x_35, x_53, x_67);
x_69 = lean_unbox_uint64(x_10);
lean_dec(x_10);
x_70 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4___redArg(x_69, x_18, x_54);
x_71 = lean_array_uset(x_68, x_53, x_70);
lean_ctor_set(x_23, 1, x_71);
x_25 = x_23;
goto block_32;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint64_t x_77; uint64_t x_78; uint64_t x_79; uint64_t x_80; uint64_t x_81; lean_object* x_82; uint64_t x_83; uint64_t x_84; uint64_t x_85; size_t x_86; size_t x_87; lean_object* x_88; size_t x_89; size_t x_90; size_t x_91; lean_object* x_92; uint64_t x_93; uint8_t x_94; 
x_72 = lean_ctor_get(x_23, 0);
x_73 = lean_ctor_get(x_23, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_23);
x_74 = lean_box(0);
lean_inc(x_1);
lean_ctor_set_tag(x_18, 1);
lean_ctor_set(x_18, 1, x_74);
lean_ctor_set(x_18, 0, x_1);
x_75 = lean_array_get_size(x_73);
x_76 = lean_unsigned_to_nat(32u);
x_77 = lean_uint64_of_nat(x_76);
x_78 = lean_unbox_uint64(x_10);
x_79 = lean_uint64_shift_right(x_78, x_77);
x_80 = lean_unbox_uint64(x_10);
x_81 = lean_uint64_xor(x_80, x_79);
x_82 = lean_unsigned_to_nat(16u);
x_83 = lean_uint64_of_nat(x_82);
x_84 = lean_uint64_shift_right(x_81, x_83);
x_85 = lean_uint64_xor(x_81, x_84);
x_86 = lean_uint64_to_usize(x_85);
x_87 = lean_usize_of_nat(x_75);
lean_dec(x_75);
x_88 = lean_unsigned_to_nat(1u);
x_89 = lean_usize_of_nat(x_88);
x_90 = lean_usize_sub(x_87, x_89);
x_91 = lean_usize_land(x_86, x_90);
x_92 = lean_array_uget(x_73, x_91);
x_93 = lean_unbox_uint64(x_10);
lean_inc(x_92);
x_94 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Canonicalizer_canon_spec__0___redArg(x_93, x_92);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_95 = lean_nat_add(x_72, x_88);
lean_dec(x_72);
x_96 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_96, 0, x_10);
lean_ctor_set(x_96, 1, x_18);
lean_ctor_set(x_96, 2, x_92);
x_97 = lean_array_uset(x_73, x_91, x_96);
x_98 = lean_unsigned_to_nat(2u);
x_99 = lean_nat_shiftl(x_95, x_98);
x_100 = lean_unsigned_to_nat(3u);
x_101 = lean_nat_div(x_99, x_100);
lean_dec(x_99);
x_102 = lean_array_get_size(x_97);
x_103 = lean_nat_dec_le(x_101, x_102);
lean_dec(x_102);
lean_dec(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1___redArg(x_97);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_95);
lean_ctor_set(x_105, 1, x_104);
x_25 = x_105;
goto block_32;
}
else
{
lean_object* x_106; 
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_95);
lean_ctor_set(x_106, 1, x_97);
x_25 = x_106;
goto block_32;
}
}
else
{
lean_object* x_107; lean_object* x_108; uint64_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_107 = lean_box(0);
x_108 = lean_array_uset(x_73, x_91, x_107);
x_109 = lean_unbox_uint64(x_10);
lean_dec(x_10);
x_110 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4___redArg(x_109, x_18, x_92);
x_111 = lean_array_uset(x_108, x_91, x_110);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_72);
lean_ctor_set(x_112, 1, x_111);
x_25 = x_112;
goto block_32;
}
}
block_32:
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_st_ref_set(x_3, x_26, x_21);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_1);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint64_t x_132; uint64_t x_133; uint64_t x_134; uint64_t x_135; uint64_t x_136; lean_object* x_137; uint64_t x_138; uint64_t x_139; uint64_t x_140; size_t x_141; size_t x_142; lean_object* x_143; size_t x_144; size_t x_145; size_t x_146; lean_object* x_147; uint64_t x_148; uint8_t x_149; 
x_113 = lean_ctor_get(x_18, 0);
x_114 = lean_ctor_get(x_18, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_18);
x_115 = lean_ctor_get(x_113, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_117 = x_113;
} else {
 lean_dec_ref(x_113);
 x_117 = lean_box(0);
}
x_125 = lean_ctor_get(x_116, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_116, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_127 = x_116;
} else {
 lean_dec_ref(x_116);
 x_127 = lean_box(0);
}
x_128 = lean_box(0);
lean_inc(x_1);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_1);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_array_get_size(x_126);
x_131 = lean_unsigned_to_nat(32u);
x_132 = lean_uint64_of_nat(x_131);
x_133 = lean_unbox_uint64(x_10);
x_134 = lean_uint64_shift_right(x_133, x_132);
x_135 = lean_unbox_uint64(x_10);
x_136 = lean_uint64_xor(x_135, x_134);
x_137 = lean_unsigned_to_nat(16u);
x_138 = lean_uint64_of_nat(x_137);
x_139 = lean_uint64_shift_right(x_136, x_138);
x_140 = lean_uint64_xor(x_136, x_139);
x_141 = lean_uint64_to_usize(x_140);
x_142 = lean_usize_of_nat(x_130);
lean_dec(x_130);
x_143 = lean_unsigned_to_nat(1u);
x_144 = lean_usize_of_nat(x_143);
x_145 = lean_usize_sub(x_142, x_144);
x_146 = lean_usize_land(x_141, x_145);
x_147 = lean_array_uget(x_126, x_146);
x_148 = lean_unbox_uint64(x_10);
lean_inc(x_147);
x_149 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Canonicalizer_canon_spec__0___redArg(x_148, x_147);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_150 = lean_nat_add(x_125, x_143);
lean_dec(x_125);
x_151 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_151, 0, x_10);
lean_ctor_set(x_151, 1, x_129);
lean_ctor_set(x_151, 2, x_147);
x_152 = lean_array_uset(x_126, x_146, x_151);
x_153 = lean_unsigned_to_nat(2u);
x_154 = lean_nat_shiftl(x_150, x_153);
x_155 = lean_unsigned_to_nat(3u);
x_156 = lean_nat_div(x_154, x_155);
lean_dec(x_154);
x_157 = lean_array_get_size(x_152);
x_158 = lean_nat_dec_le(x_156, x_157);
lean_dec(x_157);
lean_dec(x_156);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; 
x_159 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1___redArg(x_152);
if (lean_is_scalar(x_127)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_127;
}
lean_ctor_set(x_160, 0, x_150);
lean_ctor_set(x_160, 1, x_159);
x_118 = x_160;
goto block_124;
}
else
{
lean_object* x_161; 
if (lean_is_scalar(x_127)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_127;
}
lean_ctor_set(x_161, 0, x_150);
lean_ctor_set(x_161, 1, x_152);
x_118 = x_161;
goto block_124;
}
}
else
{
lean_object* x_162; lean_object* x_163; uint64_t x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_162 = lean_box(0);
x_163 = lean_array_uset(x_126, x_146, x_162);
x_164 = lean_unbox_uint64(x_10);
lean_dec(x_10);
x_165 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4___redArg(x_164, x_129, x_147);
x_166 = lean_array_uset(x_163, x_146, x_165);
if (lean_is_scalar(x_127)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_127;
}
lean_ctor_set(x_167, 0, x_125);
lean_ctor_set(x_167, 1, x_166);
x_118 = x_167;
goto block_124;
}
block_124:
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_115);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_st_ref_set(x_3, x_119, x_114);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_122 = x_120;
} else {
 lean_dec_ref(x_120);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_1);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; uint8_t x_173; uint8_t x_174; uint8_t x_175; uint8_t x_176; uint8_t x_177; uint8_t x_178; uint8_t x_179; uint8_t x_180; uint8_t x_181; uint8_t x_182; uint8_t x_183; uint8_t x_184; uint8_t x_185; uint8_t x_186; uint8_t x_187; uint8_t x_188; lean_object* x_189; uint64_t x_190; lean_object* x_191; uint64_t x_192; uint64_t x_193; uint64_t x_194; uint64_t x_195; uint64_t x_196; uint8_t x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; uint8_t x_205; lean_object* x_206; lean_object* x_207; 
x_168 = lean_ctor_get(x_17, 0);
lean_inc(x_168);
lean_dec(x_17);
x_169 = lean_box(0);
x_170 = lean_box(0);
lean_ctor_set(x_12, 1, x_170);
lean_ctor_set(x_12, 0, x_169);
x_171 = lean_ctor_get(x_4, 0);
lean_inc(x_171);
x_172 = lean_ctor_get_uint8(x_171, 0);
x_173 = lean_ctor_get_uint8(x_171, 1);
x_174 = lean_ctor_get_uint8(x_171, 2);
x_175 = lean_ctor_get_uint8(x_171, 3);
x_176 = lean_ctor_get_uint8(x_171, 4);
x_177 = lean_ctor_get_uint8(x_171, 5);
x_178 = lean_ctor_get_uint8(x_171, 6);
x_179 = lean_ctor_get_uint8(x_171, 7);
x_180 = lean_ctor_get_uint8(x_171, 8);
x_181 = lean_ctor_get_uint8(x_171, 10);
x_182 = lean_ctor_get_uint8(x_171, 11);
x_183 = lean_ctor_get_uint8(x_171, 12);
x_184 = lean_ctor_get_uint8(x_171, 13);
x_185 = lean_ctor_get_uint8(x_171, 14);
x_186 = lean_ctor_get_uint8(x_171, 15);
x_187 = lean_ctor_get_uint8(x_171, 16);
x_188 = lean_ctor_get_uint8(x_171, 17);
lean_dec(x_171);
x_189 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_189, 0, x_172);
lean_ctor_set_uint8(x_189, 1, x_173);
lean_ctor_set_uint8(x_189, 2, x_174);
lean_ctor_set_uint8(x_189, 3, x_175);
lean_ctor_set_uint8(x_189, 4, x_176);
lean_ctor_set_uint8(x_189, 5, x_177);
lean_ctor_set_uint8(x_189, 6, x_178);
lean_ctor_set_uint8(x_189, 7, x_179);
lean_ctor_set_uint8(x_189, 8, x_180);
lean_ctor_set_uint8(x_189, 9, x_2);
lean_ctor_set_uint8(x_189, 10, x_181);
lean_ctor_set_uint8(x_189, 11, x_182);
lean_ctor_set_uint8(x_189, 12, x_183);
lean_ctor_set_uint8(x_189, 13, x_184);
lean_ctor_set_uint8(x_189, 14, x_185);
lean_ctor_set_uint8(x_189, 15, x_186);
lean_ctor_set_uint8(x_189, 16, x_187);
lean_ctor_set_uint8(x_189, 17, x_188);
x_190 = lean_ctor_get_uint64(x_4, sizeof(void*)*7);
x_191 = lean_unsigned_to_nat(2u);
x_192 = lean_uint64_of_nat(x_191);
x_193 = lean_uint64_shift_right(x_190, x_192);
x_194 = lean_uint64_shift_left(x_193, x_192);
x_195 = l_Lean_Meta_TransparencyMode_toUInt64(x_2);
x_196 = lean_uint64_lor(x_194, x_195);
x_197 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 8);
x_198 = lean_ctor_get(x_4, 1);
lean_inc(x_198);
x_199 = lean_ctor_get(x_4, 2);
lean_inc(x_199);
x_200 = lean_ctor_get(x_4, 3);
lean_inc(x_200);
x_201 = lean_ctor_get(x_4, 4);
lean_inc(x_201);
x_202 = lean_ctor_get(x_4, 5);
lean_inc(x_202);
x_203 = lean_ctor_get(x_4, 6);
lean_inc(x_203);
x_204 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 9);
x_205 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 10);
lean_dec(x_4);
x_206 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_206, 0, x_189);
lean_ctor_set(x_206, 1, x_198);
lean_ctor_set(x_206, 2, x_199);
lean_ctor_set(x_206, 3, x_200);
lean_ctor_set(x_206, 4, x_201);
lean_ctor_set(x_206, 5, x_202);
lean_ctor_set(x_206, 6, x_203);
lean_ctor_set_uint64(x_206, sizeof(void*)*7, x_196);
lean_ctor_set_uint8(x_206, sizeof(void*)*7 + 8, x_197);
lean_ctor_set_uint8(x_206, sizeof(void*)*7 + 9, x_204);
lean_ctor_set_uint8(x_206, sizeof(void*)*7 + 10, x_205);
lean_inc(x_168);
lean_inc(x_1);
x_207 = l_List_forIn_x27_loop___at___Lean_Meta_Canonicalizer_canon_spec__5___redArg(x_1, x_168, x_12, x_206, x_5, x_6, x_7, x_15);
lean_dec(x_206);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
lean_dec(x_208);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; uint8_t x_212; 
x_210 = lean_ctor_get(x_207, 1);
lean_inc(x_210);
lean_dec(x_207);
x_211 = lean_st_ref_take(x_3, x_210);
x_212 = !lean_is_exclusive(x_211);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_226; 
x_213 = lean_ctor_get(x_211, 0);
x_214 = lean_ctor_get(x_211, 1);
x_215 = lean_ctor_get(x_213, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_213, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_217 = x_213;
} else {
 lean_dec_ref(x_213);
 x_217 = lean_box(0);
}
x_226 = !lean_is_exclusive(x_216);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint64_t x_231; uint64_t x_232; uint64_t x_233; uint64_t x_234; uint64_t x_235; lean_object* x_236; uint64_t x_237; uint64_t x_238; uint64_t x_239; size_t x_240; size_t x_241; lean_object* x_242; size_t x_243; size_t x_244; size_t x_245; lean_object* x_246; uint64_t x_247; uint8_t x_248; 
x_227 = lean_ctor_get(x_216, 0);
x_228 = lean_ctor_get(x_216, 1);
lean_inc(x_1);
lean_ctor_set_tag(x_211, 1);
lean_ctor_set(x_211, 1, x_168);
lean_ctor_set(x_211, 0, x_1);
x_229 = lean_array_get_size(x_228);
x_230 = lean_unsigned_to_nat(32u);
x_231 = lean_uint64_of_nat(x_230);
x_232 = lean_unbox_uint64(x_10);
x_233 = lean_uint64_shift_right(x_232, x_231);
x_234 = lean_unbox_uint64(x_10);
x_235 = lean_uint64_xor(x_234, x_233);
x_236 = lean_unsigned_to_nat(16u);
x_237 = lean_uint64_of_nat(x_236);
x_238 = lean_uint64_shift_right(x_235, x_237);
x_239 = lean_uint64_xor(x_235, x_238);
x_240 = lean_uint64_to_usize(x_239);
x_241 = lean_usize_of_nat(x_229);
lean_dec(x_229);
x_242 = lean_unsigned_to_nat(1u);
x_243 = lean_usize_of_nat(x_242);
x_244 = lean_usize_sub(x_241, x_243);
x_245 = lean_usize_land(x_240, x_244);
x_246 = lean_array_uget(x_228, x_245);
x_247 = lean_unbox_uint64(x_10);
lean_inc(x_246);
x_248 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Canonicalizer_canon_spec__0___redArg(x_247, x_246);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; 
x_249 = lean_nat_add(x_227, x_242);
lean_dec(x_227);
x_250 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_250, 0, x_10);
lean_ctor_set(x_250, 1, x_211);
lean_ctor_set(x_250, 2, x_246);
x_251 = lean_array_uset(x_228, x_245, x_250);
x_252 = lean_nat_shiftl(x_249, x_191);
x_253 = lean_unsigned_to_nat(3u);
x_254 = lean_nat_div(x_252, x_253);
lean_dec(x_252);
x_255 = lean_array_get_size(x_251);
x_256 = lean_nat_dec_le(x_254, x_255);
lean_dec(x_255);
lean_dec(x_254);
if (x_256 == 0)
{
lean_object* x_257; 
x_257 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1___redArg(x_251);
lean_ctor_set(x_216, 1, x_257);
lean_ctor_set(x_216, 0, x_249);
x_218 = x_216;
goto block_225;
}
else
{
lean_ctor_set(x_216, 1, x_251);
lean_ctor_set(x_216, 0, x_249);
x_218 = x_216;
goto block_225;
}
}
else
{
lean_object* x_258; lean_object* x_259; uint64_t x_260; lean_object* x_261; lean_object* x_262; 
x_258 = lean_box(0);
x_259 = lean_array_uset(x_228, x_245, x_258);
x_260 = lean_unbox_uint64(x_10);
lean_dec(x_10);
x_261 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4___redArg(x_260, x_211, x_246);
x_262 = lean_array_uset(x_259, x_245, x_261);
lean_ctor_set(x_216, 1, x_262);
x_218 = x_216;
goto block_225;
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; uint64_t x_267; uint64_t x_268; uint64_t x_269; uint64_t x_270; uint64_t x_271; lean_object* x_272; uint64_t x_273; uint64_t x_274; uint64_t x_275; size_t x_276; size_t x_277; lean_object* x_278; size_t x_279; size_t x_280; size_t x_281; lean_object* x_282; uint64_t x_283; uint8_t x_284; 
x_263 = lean_ctor_get(x_216, 0);
x_264 = lean_ctor_get(x_216, 1);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_216);
lean_inc(x_1);
lean_ctor_set_tag(x_211, 1);
lean_ctor_set(x_211, 1, x_168);
lean_ctor_set(x_211, 0, x_1);
x_265 = lean_array_get_size(x_264);
x_266 = lean_unsigned_to_nat(32u);
x_267 = lean_uint64_of_nat(x_266);
x_268 = lean_unbox_uint64(x_10);
x_269 = lean_uint64_shift_right(x_268, x_267);
x_270 = lean_unbox_uint64(x_10);
x_271 = lean_uint64_xor(x_270, x_269);
x_272 = lean_unsigned_to_nat(16u);
x_273 = lean_uint64_of_nat(x_272);
x_274 = lean_uint64_shift_right(x_271, x_273);
x_275 = lean_uint64_xor(x_271, x_274);
x_276 = lean_uint64_to_usize(x_275);
x_277 = lean_usize_of_nat(x_265);
lean_dec(x_265);
x_278 = lean_unsigned_to_nat(1u);
x_279 = lean_usize_of_nat(x_278);
x_280 = lean_usize_sub(x_277, x_279);
x_281 = lean_usize_land(x_276, x_280);
x_282 = lean_array_uget(x_264, x_281);
x_283 = lean_unbox_uint64(x_10);
lean_inc(x_282);
x_284 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Canonicalizer_canon_spec__0___redArg(x_283, x_282);
if (x_284 == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; 
x_285 = lean_nat_add(x_263, x_278);
lean_dec(x_263);
x_286 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_286, 0, x_10);
lean_ctor_set(x_286, 1, x_211);
lean_ctor_set(x_286, 2, x_282);
x_287 = lean_array_uset(x_264, x_281, x_286);
x_288 = lean_nat_shiftl(x_285, x_191);
x_289 = lean_unsigned_to_nat(3u);
x_290 = lean_nat_div(x_288, x_289);
lean_dec(x_288);
x_291 = lean_array_get_size(x_287);
x_292 = lean_nat_dec_le(x_290, x_291);
lean_dec(x_291);
lean_dec(x_290);
if (x_292 == 0)
{
lean_object* x_293; lean_object* x_294; 
x_293 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1___redArg(x_287);
x_294 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_294, 0, x_285);
lean_ctor_set(x_294, 1, x_293);
x_218 = x_294;
goto block_225;
}
else
{
lean_object* x_295; 
x_295 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_295, 0, x_285);
lean_ctor_set(x_295, 1, x_287);
x_218 = x_295;
goto block_225;
}
}
else
{
lean_object* x_296; lean_object* x_297; uint64_t x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_296 = lean_box(0);
x_297 = lean_array_uset(x_264, x_281, x_296);
x_298 = lean_unbox_uint64(x_10);
lean_dec(x_10);
x_299 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4___redArg(x_298, x_211, x_282);
x_300 = lean_array_uset(x_297, x_281, x_299);
x_301 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_301, 0, x_263);
lean_ctor_set(x_301, 1, x_300);
x_218 = x_301;
goto block_225;
}
}
block_225:
{
lean_object* x_219; lean_object* x_220; uint8_t x_221; 
if (lean_is_scalar(x_217)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_217;
}
lean_ctor_set(x_219, 0, x_215);
lean_ctor_set(x_219, 1, x_218);
x_220 = lean_st_ref_set(x_3, x_219, x_214);
x_221 = !lean_is_exclusive(x_220);
if (x_221 == 0)
{
lean_object* x_222; 
x_222 = lean_ctor_get(x_220, 0);
lean_dec(x_222);
lean_ctor_set(x_220, 0, x_1);
return x_220;
}
else
{
lean_object* x_223; lean_object* x_224; 
x_223 = lean_ctor_get(x_220, 1);
lean_inc(x_223);
lean_dec(x_220);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_1);
lean_ctor_set(x_224, 1, x_223);
return x_224;
}
}
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint64_t x_320; uint64_t x_321; uint64_t x_322; uint64_t x_323; uint64_t x_324; lean_object* x_325; uint64_t x_326; uint64_t x_327; uint64_t x_328; size_t x_329; size_t x_330; lean_object* x_331; size_t x_332; size_t x_333; size_t x_334; lean_object* x_335; uint64_t x_336; uint8_t x_337; 
x_302 = lean_ctor_get(x_211, 0);
x_303 = lean_ctor_get(x_211, 1);
lean_inc(x_303);
lean_inc(x_302);
lean_dec(x_211);
x_304 = lean_ctor_get(x_302, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_302, 1);
lean_inc(x_305);
if (lean_is_exclusive(x_302)) {
 lean_ctor_release(x_302, 0);
 lean_ctor_release(x_302, 1);
 x_306 = x_302;
} else {
 lean_dec_ref(x_302);
 x_306 = lean_box(0);
}
x_314 = lean_ctor_get(x_305, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_305, 1);
lean_inc(x_315);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 lean_ctor_release(x_305, 1);
 x_316 = x_305;
} else {
 lean_dec_ref(x_305);
 x_316 = lean_box(0);
}
lean_inc(x_1);
x_317 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_317, 0, x_1);
lean_ctor_set(x_317, 1, x_168);
x_318 = lean_array_get_size(x_315);
x_319 = lean_unsigned_to_nat(32u);
x_320 = lean_uint64_of_nat(x_319);
x_321 = lean_unbox_uint64(x_10);
x_322 = lean_uint64_shift_right(x_321, x_320);
x_323 = lean_unbox_uint64(x_10);
x_324 = lean_uint64_xor(x_323, x_322);
x_325 = lean_unsigned_to_nat(16u);
x_326 = lean_uint64_of_nat(x_325);
x_327 = lean_uint64_shift_right(x_324, x_326);
x_328 = lean_uint64_xor(x_324, x_327);
x_329 = lean_uint64_to_usize(x_328);
x_330 = lean_usize_of_nat(x_318);
lean_dec(x_318);
x_331 = lean_unsigned_to_nat(1u);
x_332 = lean_usize_of_nat(x_331);
x_333 = lean_usize_sub(x_330, x_332);
x_334 = lean_usize_land(x_329, x_333);
x_335 = lean_array_uget(x_315, x_334);
x_336 = lean_unbox_uint64(x_10);
lean_inc(x_335);
x_337 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Canonicalizer_canon_spec__0___redArg(x_336, x_335);
if (x_337 == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; uint8_t x_345; 
x_338 = lean_nat_add(x_314, x_331);
lean_dec(x_314);
x_339 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_339, 0, x_10);
lean_ctor_set(x_339, 1, x_317);
lean_ctor_set(x_339, 2, x_335);
x_340 = lean_array_uset(x_315, x_334, x_339);
x_341 = lean_nat_shiftl(x_338, x_191);
x_342 = lean_unsigned_to_nat(3u);
x_343 = lean_nat_div(x_341, x_342);
lean_dec(x_341);
x_344 = lean_array_get_size(x_340);
x_345 = lean_nat_dec_le(x_343, x_344);
lean_dec(x_344);
lean_dec(x_343);
if (x_345 == 0)
{
lean_object* x_346; lean_object* x_347; 
x_346 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1___redArg(x_340);
if (lean_is_scalar(x_316)) {
 x_347 = lean_alloc_ctor(0, 2, 0);
} else {
 x_347 = x_316;
}
lean_ctor_set(x_347, 0, x_338);
lean_ctor_set(x_347, 1, x_346);
x_307 = x_347;
goto block_313;
}
else
{
lean_object* x_348; 
if (lean_is_scalar(x_316)) {
 x_348 = lean_alloc_ctor(0, 2, 0);
} else {
 x_348 = x_316;
}
lean_ctor_set(x_348, 0, x_338);
lean_ctor_set(x_348, 1, x_340);
x_307 = x_348;
goto block_313;
}
}
else
{
lean_object* x_349; lean_object* x_350; uint64_t x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_349 = lean_box(0);
x_350 = lean_array_uset(x_315, x_334, x_349);
x_351 = lean_unbox_uint64(x_10);
lean_dec(x_10);
x_352 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4___redArg(x_351, x_317, x_335);
x_353 = lean_array_uset(x_350, x_334, x_352);
if (lean_is_scalar(x_316)) {
 x_354 = lean_alloc_ctor(0, 2, 0);
} else {
 x_354 = x_316;
}
lean_ctor_set(x_354, 0, x_314);
lean_ctor_set(x_354, 1, x_353);
x_307 = x_354;
goto block_313;
}
block_313:
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
if (lean_is_scalar(x_306)) {
 x_308 = lean_alloc_ctor(0, 2, 0);
} else {
 x_308 = x_306;
}
lean_ctor_set(x_308, 0, x_304);
lean_ctor_set(x_308, 1, x_307);
x_309 = lean_st_ref_set(x_3, x_308, x_303);
x_310 = lean_ctor_get(x_309, 1);
lean_inc(x_310);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 lean_ctor_release(x_309, 1);
 x_311 = x_309;
} else {
 lean_dec_ref(x_309);
 x_311 = lean_box(0);
}
if (lean_is_scalar(x_311)) {
 x_312 = lean_alloc_ctor(0, 2, 0);
} else {
 x_312 = x_311;
}
lean_ctor_set(x_312, 0, x_1);
lean_ctor_set(x_312, 1, x_310);
return x_312;
}
}
}
else
{
uint8_t x_355; 
lean_dec(x_168);
lean_dec(x_10);
lean_dec(x_1);
x_355 = !lean_is_exclusive(x_207);
if (x_355 == 0)
{
lean_object* x_356; lean_object* x_357; 
x_356 = lean_ctor_get(x_207, 0);
lean_dec(x_356);
x_357 = lean_ctor_get(x_209, 0);
lean_inc(x_357);
lean_dec(x_209);
lean_ctor_set(x_207, 0, x_357);
return x_207;
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_358 = lean_ctor_get(x_207, 1);
lean_inc(x_358);
lean_dec(x_207);
x_359 = lean_ctor_get(x_209, 0);
lean_inc(x_359);
lean_dec(x_209);
x_360 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_358);
return x_360;
}
}
}
else
{
uint8_t x_361; 
lean_dec(x_168);
lean_dec(x_10);
lean_dec(x_1);
x_361 = !lean_is_exclusive(x_207);
if (x_361 == 0)
{
return x_207;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_362 = lean_ctor_get(x_207, 0);
x_363 = lean_ctor_get(x_207, 1);
lean_inc(x_363);
lean_inc(x_362);
lean_dec(x_207);
x_364 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_364, 0, x_362);
lean_ctor_set(x_364, 1, x_363);
return x_364;
}
}
}
}
else
{
lean_object* x_365; lean_object* x_366; uint64_t x_367; lean_object* x_368; 
x_365 = lean_ctor_get(x_12, 0);
x_366 = lean_ctor_get(x_12, 1);
lean_inc(x_366);
lean_inc(x_365);
lean_dec(x_12);
x_367 = lean_unbox_uint64(x_10);
x_368 = l_Lean_Meta_Canonicalizer_canon_unsafe__1(x_367, x_365);
lean_dec(x_365);
if (lean_obj_tag(x_368) == 0)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; uint64_t x_390; uint64_t x_391; uint64_t x_392; uint64_t x_393; uint64_t x_394; lean_object* x_395; uint64_t x_396; uint64_t x_397; uint64_t x_398; size_t x_399; size_t x_400; lean_object* x_401; size_t x_402; size_t x_403; size_t x_404; lean_object* x_405; uint64_t x_406; uint8_t x_407; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_369 = lean_st_ref_take(x_3, x_366);
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_369, 1);
lean_inc(x_371);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 lean_ctor_release(x_369, 1);
 x_372 = x_369;
} else {
 lean_dec_ref(x_369);
 x_372 = lean_box(0);
}
x_373 = lean_ctor_get(x_370, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_370, 1);
lean_inc(x_374);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 lean_ctor_release(x_370, 1);
 x_375 = x_370;
} else {
 lean_dec_ref(x_370);
 x_375 = lean_box(0);
}
x_383 = lean_ctor_get(x_374, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_374, 1);
lean_inc(x_384);
if (lean_is_exclusive(x_374)) {
 lean_ctor_release(x_374, 0);
 lean_ctor_release(x_374, 1);
 x_385 = x_374;
} else {
 lean_dec_ref(x_374);
 x_385 = lean_box(0);
}
x_386 = lean_box(0);
lean_inc(x_1);
if (lean_is_scalar(x_372)) {
 x_387 = lean_alloc_ctor(1, 2, 0);
} else {
 x_387 = x_372;
 lean_ctor_set_tag(x_387, 1);
}
lean_ctor_set(x_387, 0, x_1);
lean_ctor_set(x_387, 1, x_386);
x_388 = lean_array_get_size(x_384);
x_389 = lean_unsigned_to_nat(32u);
x_390 = lean_uint64_of_nat(x_389);
x_391 = lean_unbox_uint64(x_10);
x_392 = lean_uint64_shift_right(x_391, x_390);
x_393 = lean_unbox_uint64(x_10);
x_394 = lean_uint64_xor(x_393, x_392);
x_395 = lean_unsigned_to_nat(16u);
x_396 = lean_uint64_of_nat(x_395);
x_397 = lean_uint64_shift_right(x_394, x_396);
x_398 = lean_uint64_xor(x_394, x_397);
x_399 = lean_uint64_to_usize(x_398);
x_400 = lean_usize_of_nat(x_388);
lean_dec(x_388);
x_401 = lean_unsigned_to_nat(1u);
x_402 = lean_usize_of_nat(x_401);
x_403 = lean_usize_sub(x_400, x_402);
x_404 = lean_usize_land(x_399, x_403);
x_405 = lean_array_uget(x_384, x_404);
x_406 = lean_unbox_uint64(x_10);
lean_inc(x_405);
x_407 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Canonicalizer_canon_spec__0___redArg(x_406, x_405);
if (x_407 == 0)
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; uint8_t x_416; 
x_408 = lean_nat_add(x_383, x_401);
lean_dec(x_383);
x_409 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_409, 0, x_10);
lean_ctor_set(x_409, 1, x_387);
lean_ctor_set(x_409, 2, x_405);
x_410 = lean_array_uset(x_384, x_404, x_409);
x_411 = lean_unsigned_to_nat(2u);
x_412 = lean_nat_shiftl(x_408, x_411);
x_413 = lean_unsigned_to_nat(3u);
x_414 = lean_nat_div(x_412, x_413);
lean_dec(x_412);
x_415 = lean_array_get_size(x_410);
x_416 = lean_nat_dec_le(x_414, x_415);
lean_dec(x_415);
lean_dec(x_414);
if (x_416 == 0)
{
lean_object* x_417; lean_object* x_418; 
x_417 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1___redArg(x_410);
if (lean_is_scalar(x_385)) {
 x_418 = lean_alloc_ctor(0, 2, 0);
} else {
 x_418 = x_385;
}
lean_ctor_set(x_418, 0, x_408);
lean_ctor_set(x_418, 1, x_417);
x_376 = x_418;
goto block_382;
}
else
{
lean_object* x_419; 
if (lean_is_scalar(x_385)) {
 x_419 = lean_alloc_ctor(0, 2, 0);
} else {
 x_419 = x_385;
}
lean_ctor_set(x_419, 0, x_408);
lean_ctor_set(x_419, 1, x_410);
x_376 = x_419;
goto block_382;
}
}
else
{
lean_object* x_420; lean_object* x_421; uint64_t x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_420 = lean_box(0);
x_421 = lean_array_uset(x_384, x_404, x_420);
x_422 = lean_unbox_uint64(x_10);
lean_dec(x_10);
x_423 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4___redArg(x_422, x_387, x_405);
x_424 = lean_array_uset(x_421, x_404, x_423);
if (lean_is_scalar(x_385)) {
 x_425 = lean_alloc_ctor(0, 2, 0);
} else {
 x_425 = x_385;
}
lean_ctor_set(x_425, 0, x_383);
lean_ctor_set(x_425, 1, x_424);
x_376 = x_425;
goto block_382;
}
block_382:
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
if (lean_is_scalar(x_375)) {
 x_377 = lean_alloc_ctor(0, 2, 0);
} else {
 x_377 = x_375;
}
lean_ctor_set(x_377, 0, x_373);
lean_ctor_set(x_377, 1, x_376);
x_378 = lean_st_ref_set(x_3, x_377, x_371);
x_379 = lean_ctor_get(x_378, 1);
lean_inc(x_379);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 x_380 = x_378;
} else {
 lean_dec_ref(x_378);
 x_380 = lean_box(0);
}
if (lean_is_scalar(x_380)) {
 x_381 = lean_alloc_ctor(0, 2, 0);
} else {
 x_381 = x_380;
}
lean_ctor_set(x_381, 0, x_1);
lean_ctor_set(x_381, 1, x_379);
return x_381;
}
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; uint8_t x_431; uint8_t x_432; uint8_t x_433; uint8_t x_434; uint8_t x_435; uint8_t x_436; uint8_t x_437; uint8_t x_438; uint8_t x_439; uint8_t x_440; uint8_t x_441; uint8_t x_442; uint8_t x_443; uint8_t x_444; uint8_t x_445; uint8_t x_446; uint8_t x_447; lean_object* x_448; uint64_t x_449; lean_object* x_450; uint64_t x_451; uint64_t x_452; uint64_t x_453; uint64_t x_454; uint64_t x_455; uint8_t x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; uint8_t x_463; uint8_t x_464; lean_object* x_465; lean_object* x_466; 
x_426 = lean_ctor_get(x_368, 0);
lean_inc(x_426);
lean_dec(x_368);
x_427 = lean_box(0);
x_428 = lean_box(0);
x_429 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_429, 0, x_427);
lean_ctor_set(x_429, 1, x_428);
x_430 = lean_ctor_get(x_4, 0);
lean_inc(x_430);
x_431 = lean_ctor_get_uint8(x_430, 0);
x_432 = lean_ctor_get_uint8(x_430, 1);
x_433 = lean_ctor_get_uint8(x_430, 2);
x_434 = lean_ctor_get_uint8(x_430, 3);
x_435 = lean_ctor_get_uint8(x_430, 4);
x_436 = lean_ctor_get_uint8(x_430, 5);
x_437 = lean_ctor_get_uint8(x_430, 6);
x_438 = lean_ctor_get_uint8(x_430, 7);
x_439 = lean_ctor_get_uint8(x_430, 8);
x_440 = lean_ctor_get_uint8(x_430, 10);
x_441 = lean_ctor_get_uint8(x_430, 11);
x_442 = lean_ctor_get_uint8(x_430, 12);
x_443 = lean_ctor_get_uint8(x_430, 13);
x_444 = lean_ctor_get_uint8(x_430, 14);
x_445 = lean_ctor_get_uint8(x_430, 15);
x_446 = lean_ctor_get_uint8(x_430, 16);
x_447 = lean_ctor_get_uint8(x_430, 17);
lean_dec(x_430);
x_448 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_448, 0, x_431);
lean_ctor_set_uint8(x_448, 1, x_432);
lean_ctor_set_uint8(x_448, 2, x_433);
lean_ctor_set_uint8(x_448, 3, x_434);
lean_ctor_set_uint8(x_448, 4, x_435);
lean_ctor_set_uint8(x_448, 5, x_436);
lean_ctor_set_uint8(x_448, 6, x_437);
lean_ctor_set_uint8(x_448, 7, x_438);
lean_ctor_set_uint8(x_448, 8, x_439);
lean_ctor_set_uint8(x_448, 9, x_2);
lean_ctor_set_uint8(x_448, 10, x_440);
lean_ctor_set_uint8(x_448, 11, x_441);
lean_ctor_set_uint8(x_448, 12, x_442);
lean_ctor_set_uint8(x_448, 13, x_443);
lean_ctor_set_uint8(x_448, 14, x_444);
lean_ctor_set_uint8(x_448, 15, x_445);
lean_ctor_set_uint8(x_448, 16, x_446);
lean_ctor_set_uint8(x_448, 17, x_447);
x_449 = lean_ctor_get_uint64(x_4, sizeof(void*)*7);
x_450 = lean_unsigned_to_nat(2u);
x_451 = lean_uint64_of_nat(x_450);
x_452 = lean_uint64_shift_right(x_449, x_451);
x_453 = lean_uint64_shift_left(x_452, x_451);
x_454 = l_Lean_Meta_TransparencyMode_toUInt64(x_2);
x_455 = lean_uint64_lor(x_453, x_454);
x_456 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 8);
x_457 = lean_ctor_get(x_4, 1);
lean_inc(x_457);
x_458 = lean_ctor_get(x_4, 2);
lean_inc(x_458);
x_459 = lean_ctor_get(x_4, 3);
lean_inc(x_459);
x_460 = lean_ctor_get(x_4, 4);
lean_inc(x_460);
x_461 = lean_ctor_get(x_4, 5);
lean_inc(x_461);
x_462 = lean_ctor_get(x_4, 6);
lean_inc(x_462);
x_463 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 9);
x_464 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 10);
lean_dec(x_4);
x_465 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_465, 0, x_448);
lean_ctor_set(x_465, 1, x_457);
lean_ctor_set(x_465, 2, x_458);
lean_ctor_set(x_465, 3, x_459);
lean_ctor_set(x_465, 4, x_460);
lean_ctor_set(x_465, 5, x_461);
lean_ctor_set(x_465, 6, x_462);
lean_ctor_set_uint64(x_465, sizeof(void*)*7, x_455);
lean_ctor_set_uint8(x_465, sizeof(void*)*7 + 8, x_456);
lean_ctor_set_uint8(x_465, sizeof(void*)*7 + 9, x_463);
lean_ctor_set_uint8(x_465, sizeof(void*)*7 + 10, x_464);
lean_inc(x_426);
lean_inc(x_1);
x_466 = l_List_forIn_x27_loop___at___Lean_Meta_Canonicalizer_canon_spec__5___redArg(x_1, x_426, x_429, x_465, x_5, x_6, x_7, x_366);
lean_dec(x_465);
if (lean_obj_tag(x_466) == 0)
{
lean_object* x_467; lean_object* x_468; 
x_467 = lean_ctor_get(x_466, 0);
lean_inc(x_467);
x_468 = lean_ctor_get(x_467, 0);
lean_inc(x_468);
lean_dec(x_467);
if (lean_obj_tag(x_468) == 0)
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; uint64_t x_490; uint64_t x_491; uint64_t x_492; uint64_t x_493; uint64_t x_494; lean_object* x_495; uint64_t x_496; uint64_t x_497; uint64_t x_498; size_t x_499; size_t x_500; lean_object* x_501; size_t x_502; size_t x_503; size_t x_504; lean_object* x_505; uint64_t x_506; uint8_t x_507; 
x_469 = lean_ctor_get(x_466, 1);
lean_inc(x_469);
lean_dec(x_466);
x_470 = lean_st_ref_take(x_3, x_469);
x_471 = lean_ctor_get(x_470, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_470, 1);
lean_inc(x_472);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 lean_ctor_release(x_470, 1);
 x_473 = x_470;
} else {
 lean_dec_ref(x_470);
 x_473 = lean_box(0);
}
x_474 = lean_ctor_get(x_471, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_471, 1);
lean_inc(x_475);
if (lean_is_exclusive(x_471)) {
 lean_ctor_release(x_471, 0);
 lean_ctor_release(x_471, 1);
 x_476 = x_471;
} else {
 lean_dec_ref(x_471);
 x_476 = lean_box(0);
}
x_484 = lean_ctor_get(x_475, 0);
lean_inc(x_484);
x_485 = lean_ctor_get(x_475, 1);
lean_inc(x_485);
if (lean_is_exclusive(x_475)) {
 lean_ctor_release(x_475, 0);
 lean_ctor_release(x_475, 1);
 x_486 = x_475;
} else {
 lean_dec_ref(x_475);
 x_486 = lean_box(0);
}
lean_inc(x_1);
if (lean_is_scalar(x_473)) {
 x_487 = lean_alloc_ctor(1, 2, 0);
} else {
 x_487 = x_473;
 lean_ctor_set_tag(x_487, 1);
}
lean_ctor_set(x_487, 0, x_1);
lean_ctor_set(x_487, 1, x_426);
x_488 = lean_array_get_size(x_485);
x_489 = lean_unsigned_to_nat(32u);
x_490 = lean_uint64_of_nat(x_489);
x_491 = lean_unbox_uint64(x_10);
x_492 = lean_uint64_shift_right(x_491, x_490);
x_493 = lean_unbox_uint64(x_10);
x_494 = lean_uint64_xor(x_493, x_492);
x_495 = lean_unsigned_to_nat(16u);
x_496 = lean_uint64_of_nat(x_495);
x_497 = lean_uint64_shift_right(x_494, x_496);
x_498 = lean_uint64_xor(x_494, x_497);
x_499 = lean_uint64_to_usize(x_498);
x_500 = lean_usize_of_nat(x_488);
lean_dec(x_488);
x_501 = lean_unsigned_to_nat(1u);
x_502 = lean_usize_of_nat(x_501);
x_503 = lean_usize_sub(x_500, x_502);
x_504 = lean_usize_land(x_499, x_503);
x_505 = lean_array_uget(x_485, x_504);
x_506 = lean_unbox_uint64(x_10);
lean_inc(x_505);
x_507 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Canonicalizer_canon_spec__0___redArg(x_506, x_505);
if (x_507 == 0)
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; uint8_t x_515; 
x_508 = lean_nat_add(x_484, x_501);
lean_dec(x_484);
x_509 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_509, 0, x_10);
lean_ctor_set(x_509, 1, x_487);
lean_ctor_set(x_509, 2, x_505);
x_510 = lean_array_uset(x_485, x_504, x_509);
x_511 = lean_nat_shiftl(x_508, x_450);
x_512 = lean_unsigned_to_nat(3u);
x_513 = lean_nat_div(x_511, x_512);
lean_dec(x_511);
x_514 = lean_array_get_size(x_510);
x_515 = lean_nat_dec_le(x_513, x_514);
lean_dec(x_514);
lean_dec(x_513);
if (x_515 == 0)
{
lean_object* x_516; lean_object* x_517; 
x_516 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1___redArg(x_510);
if (lean_is_scalar(x_486)) {
 x_517 = lean_alloc_ctor(0, 2, 0);
} else {
 x_517 = x_486;
}
lean_ctor_set(x_517, 0, x_508);
lean_ctor_set(x_517, 1, x_516);
x_477 = x_517;
goto block_483;
}
else
{
lean_object* x_518; 
if (lean_is_scalar(x_486)) {
 x_518 = lean_alloc_ctor(0, 2, 0);
} else {
 x_518 = x_486;
}
lean_ctor_set(x_518, 0, x_508);
lean_ctor_set(x_518, 1, x_510);
x_477 = x_518;
goto block_483;
}
}
else
{
lean_object* x_519; lean_object* x_520; uint64_t x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; 
x_519 = lean_box(0);
x_520 = lean_array_uset(x_485, x_504, x_519);
x_521 = lean_unbox_uint64(x_10);
lean_dec(x_10);
x_522 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4___redArg(x_521, x_487, x_505);
x_523 = lean_array_uset(x_520, x_504, x_522);
if (lean_is_scalar(x_486)) {
 x_524 = lean_alloc_ctor(0, 2, 0);
} else {
 x_524 = x_486;
}
lean_ctor_set(x_524, 0, x_484);
lean_ctor_set(x_524, 1, x_523);
x_477 = x_524;
goto block_483;
}
block_483:
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
if (lean_is_scalar(x_476)) {
 x_478 = lean_alloc_ctor(0, 2, 0);
} else {
 x_478 = x_476;
}
lean_ctor_set(x_478, 0, x_474);
lean_ctor_set(x_478, 1, x_477);
x_479 = lean_st_ref_set(x_3, x_478, x_472);
x_480 = lean_ctor_get(x_479, 1);
lean_inc(x_480);
if (lean_is_exclusive(x_479)) {
 lean_ctor_release(x_479, 0);
 lean_ctor_release(x_479, 1);
 x_481 = x_479;
} else {
 lean_dec_ref(x_479);
 x_481 = lean_box(0);
}
if (lean_is_scalar(x_481)) {
 x_482 = lean_alloc_ctor(0, 2, 0);
} else {
 x_482 = x_481;
}
lean_ctor_set(x_482, 0, x_1);
lean_ctor_set(x_482, 1, x_480);
return x_482;
}
}
else
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; 
lean_dec(x_426);
lean_dec(x_10);
lean_dec(x_1);
x_525 = lean_ctor_get(x_466, 1);
lean_inc(x_525);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 lean_ctor_release(x_466, 1);
 x_526 = x_466;
} else {
 lean_dec_ref(x_466);
 x_526 = lean_box(0);
}
x_527 = lean_ctor_get(x_468, 0);
lean_inc(x_527);
lean_dec(x_468);
if (lean_is_scalar(x_526)) {
 x_528 = lean_alloc_ctor(0, 2, 0);
} else {
 x_528 = x_526;
}
lean_ctor_set(x_528, 0, x_527);
lean_ctor_set(x_528, 1, x_525);
return x_528;
}
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; 
lean_dec(x_426);
lean_dec(x_10);
lean_dec(x_1);
x_529 = lean_ctor_get(x_466, 0);
lean_inc(x_529);
x_530 = lean_ctor_get(x_466, 1);
lean_inc(x_530);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 lean_ctor_release(x_466, 1);
 x_531 = x_466;
} else {
 lean_dec_ref(x_466);
 x_531 = lean_box(0);
}
if (lean_is_scalar(x_531)) {
 x_532 = lean_alloc_ctor(1, 2, 0);
} else {
 x_532 = x_531;
}
lean_ctor_set(x_532, 0, x_529);
lean_ctor_set(x_532, 1, x_530);
return x_532;
}
}
}
}
else
{
uint8_t x_533; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_533 = !lean_is_exclusive(x_9);
if (x_533 == 0)
{
return x_9;
}
else
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; 
x_534 = lean_ctor_get(x_9, 0);
x_535 = lean_ctor_get(x_9, 1);
lean_inc(x_535);
lean_inc(x_534);
lean_dec(x_9);
x_536 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_536, 0, x_534);
lean_ctor_set(x_536, 1, x_535);
return x_536;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Canonicalizer_canon_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Canonicalizer_canon_spec__0___redArg(x_3, x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Canonicalizer_canon_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Canonicalizer_canon_spec__0(x_1, x_4, x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4___redArg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_6 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Canonicalizer_canon_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forIn_x27_loop___at___Lean_Meta_Canonicalizer_canon_spec__5___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Canonicalizer_canon_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_List_forIn_x27_loop___at___Lean_Meta_Canonicalizer_canon_spec__5(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_Canonicalizer_canon(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_10;
}
}
lean_object* initialize_Lean_Util_ShareCommon(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_FunInfo(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_HashMap_Raw(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Canonicalizer(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_ShareCommon(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_FunInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap_Raw(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Canonicalizer_instInhabitedExprVisited = _init_l_Lean_Meta_Canonicalizer_instInhabitedExprVisited();
lean_mark_persistent(l_Lean_Meta_Canonicalizer_instInhabitedExprVisited);
l_Lean_Meta_Canonicalizer_instBEqExprVisited = _init_l_Lean_Meta_Canonicalizer_instBEqExprVisited();
lean_mark_persistent(l_Lean_Meta_Canonicalizer_instBEqExprVisited);
l_Lean_Meta_Canonicalizer_instHashableExprVisited = _init_l_Lean_Meta_Canonicalizer_instHashableExprVisited();
lean_mark_persistent(l_Lean_Meta_Canonicalizer_instHashableExprVisited);
l_Lean_Meta_Canonicalizer_instInhabitedState = _init_l_Lean_Meta_Canonicalizer_instInhabitedState();
lean_mark_persistent(l_Lean_Meta_Canonicalizer_instInhabitedState);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
