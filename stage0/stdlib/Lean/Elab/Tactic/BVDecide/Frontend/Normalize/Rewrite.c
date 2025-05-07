// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Rewrite
// Imports: Lean.Elab.Tactic.Simp Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Basic Lean.Elab.Tactic.BVDecide.Frontend.Attr
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
lean_object* l_Lean_Meta_getSEvalTheorems(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_bvNormalizeExt;
extern lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_bvNormalizeSimprocExt;
uint8_t l_Array_isEmpty___redArg(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_Meta_getSimpCongrTheorems(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpGoal(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_MVarId_getNondepPropHyps_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getPropHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_getSEvalSimprocs(lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_SimprocExtension_getSimprocs___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_MVarId_getNondepPropHyps_spec__6___redArg(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_SimpExtension_getTheorems___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_14; 
x_14 = lean_usize_dec_eq(x_2, x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint64_t x_22; lean_object* x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; lean_object* x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; size_t x_31; size_t x_32; lean_object* x_33; size_t x_34; size_t x_35; size_t x_36; lean_object* x_37; uint8_t x_38; 
x_15 = lean_st_ref_get(x_5, x_6);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_array_uget(x_1, x_2);
x_21 = lean_array_get_size(x_19);
x_22 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_20);
x_23 = lean_unsigned_to_nat(32u);
x_24 = lean_uint64_of_nat(x_23);
x_25 = lean_uint64_shift_right(x_22, x_24);
x_26 = lean_uint64_xor(x_22, x_25);
x_27 = lean_unsigned_to_nat(16u);
x_28 = lean_uint64_of_nat(x_27);
x_29 = lean_uint64_shift_right(x_26, x_28);
x_30 = lean_uint64_xor(x_26, x_29);
x_31 = lean_uint64_to_usize(x_30);
x_32 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_usize_of_nat(x_33);
x_35 = lean_usize_sub(x_32, x_34);
x_36 = lean_usize_land(x_31, x_35);
x_37 = lean_array_uget(x_19, x_36);
lean_dec(x_19);
x_38 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_MVarId_getNondepPropHyps_spec__0___redArg(x_20, x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_array_push(x_4, x_20);
x_7 = x_39;
x_8 = x_18;
goto block_13;
}
else
{
lean_dec(x_20);
x_7 = x_4;
x_8 = x_18;
goto block_13;
}
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_4);
lean_ctor_set(x_40, 1, x_6);
return x_40;
}
block_13:
{
lean_object* x_9; size_t x_10; size_t x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
x_4 = x_7;
x_6 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_6, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_19; 
x_19 = lean_usize_dec_eq(x_2, x_3);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint64_t x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; lean_object* x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; size_t x_36; size_t x_37; lean_object* x_38; size_t x_39; size_t x_40; size_t x_41; lean_object* x_42; uint8_t x_43; 
x_20 = lean_st_ref_get(x_6, x_11);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_array_uget(x_1, x_2);
x_26 = lean_array_get_size(x_24);
x_27 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_25);
x_28 = lean_unsigned_to_nat(32u);
x_29 = lean_uint64_of_nat(x_28);
x_30 = lean_uint64_shift_right(x_27, x_29);
x_31 = lean_uint64_xor(x_27, x_30);
x_32 = lean_unsigned_to_nat(16u);
x_33 = lean_uint64_of_nat(x_32);
x_34 = lean_uint64_shift_right(x_31, x_33);
x_35 = lean_uint64_xor(x_31, x_34);
x_36 = lean_uint64_to_usize(x_35);
x_37 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_usize_of_nat(x_38);
x_40 = lean_usize_sub(x_37, x_39);
x_41 = lean_usize_land(x_36, x_40);
x_42 = lean_array_uget(x_24, x_41);
lean_dec(x_24);
x_43 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_MVarId_getNondepPropHyps_spec__0___redArg(x_25, x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_array_push(x_4, x_25);
x_12 = x_44;
x_13 = x_23;
goto block_18;
}
else
{
lean_dec(x_25);
x_12 = x_4;
x_13 = x_23;
goto block_18;
}
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_4);
lean_ctor_set(x_45, 1, x_11);
return x_45;
}
block_18:
{
lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_2, x_15);
x_17 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0___redArg(x_1, x_16, x_3, x_12, x_6, x_13);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__2___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__2___redArg___lam__0), 8, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), x_1, x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_Meta_getPropHyps(x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_10);
x_14 = lean_mk_empty_array_with_capacity(x_12);
x_15 = lean_nat_dec_lt(x_12, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_13, x_13);
if (x_16 == 0)
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
lean_free_object(x_8);
x_17 = lean_usize_of_nat(x_12);
x_18 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_19 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__0(x_10, x_17, x_18, x_14, x_1, x_2, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_10);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_array_get_size(x_20);
x_24 = lean_mk_empty_array_with_capacity(x_22);
x_25 = lean_nat_dec_lt(x_22, x_23);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_21);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = lean_nat_dec_le(x_23, x_23);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_21);
return x_28;
}
else
{
size_t x_29; size_t x_30; lean_object* x_31; 
x_29 = lean_usize_of_nat(x_22);
x_30 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_31 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__0(x_20, x_29, x_30, x_24, x_1, x_2, x_3, x_4, x_5, x_6, x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_20);
return x_31;
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
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps___lam__0___boxed), 7, 0);
x_10 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__2___redArg(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0___redArg(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__0(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_27; uint64_t x_28; lean_object* x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; lean_object* x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; size_t x_37; size_t x_38; lean_object* x_39; size_t x_40; size_t x_41; size_t x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_4);
x_8 = lean_st_ref_take(x_5, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
x_14 = lean_array_uget(x_1, x_2);
x_15 = lean_box(0);
x_27 = lean_array_get_size(x_13);
x_28 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_14);
x_29 = lean_unsigned_to_nat(32u);
x_30 = lean_uint64_of_nat(x_29);
x_31 = lean_uint64_shift_right(x_28, x_30);
x_32 = lean_uint64_xor(x_28, x_31);
x_33 = lean_unsigned_to_nat(16u);
x_34 = lean_uint64_of_nat(x_33);
x_35 = lean_uint64_shift_right(x_32, x_34);
x_36 = lean_uint64_xor(x_32, x_35);
x_37 = lean_uint64_to_usize(x_36);
x_38 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_usize_of_nat(x_39);
x_41 = lean_usize_sub(x_38, x_40);
x_42 = lean_usize_land(x_37, x_41);
x_43 = lean_array_uget(x_13, x_42);
x_44 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_MVarId_getNondepPropHyps_spec__0___redArg(x_14, x_43);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_10);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_46 = lean_ctor_get(x_10, 1);
lean_dec(x_46);
x_47 = lean_ctor_get(x_10, 0);
lean_dec(x_47);
x_48 = lean_nat_add(x_12, x_39);
lean_dec(x_12);
x_49 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_49, 0, x_14);
lean_ctor_set(x_49, 1, x_15);
lean_ctor_set(x_49, 2, x_43);
x_50 = lean_array_uset(x_13, x_42, x_49);
x_51 = lean_unsigned_to_nat(2u);
x_52 = lean_nat_shiftl(x_48, x_51);
x_53 = lean_unsigned_to_nat(3u);
x_54 = lean_nat_div(x_52, x_53);
lean_dec(x_52);
x_55 = lean_array_get_size(x_50);
x_56 = lean_nat_dec_le(x_54, x_55);
lean_dec(x_55);
lean_dec(x_54);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_MVarId_getNondepPropHyps_spec__6___redArg(x_50);
lean_ctor_set(x_10, 1, x_57);
lean_ctor_set(x_10, 0, x_48);
x_16 = x_10;
goto block_26;
}
else
{
lean_ctor_set(x_10, 1, x_50);
lean_ctor_set(x_10, 0, x_48);
x_16 = x_10;
goto block_26;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
lean_dec(x_10);
x_58 = lean_nat_add(x_12, x_39);
lean_dec(x_12);
x_59 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_59, 0, x_14);
lean_ctor_set(x_59, 1, x_15);
lean_ctor_set(x_59, 2, x_43);
x_60 = lean_array_uset(x_13, x_42, x_59);
x_61 = lean_unsigned_to_nat(2u);
x_62 = lean_nat_shiftl(x_58, x_61);
x_63 = lean_unsigned_to_nat(3u);
x_64 = lean_nat_div(x_62, x_63);
lean_dec(x_62);
x_65 = lean_array_get_size(x_60);
x_66 = lean_nat_dec_le(x_64, x_65);
lean_dec(x_65);
lean_dec(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_MVarId_getNondepPropHyps_spec__6___redArg(x_60);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_58);
lean_ctor_set(x_68, 1, x_67);
x_16 = x_68;
goto block_26;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_58);
lean_ctor_set(x_69, 1, x_60);
x_16 = x_69;
goto block_26;
}
}
}
else
{
lean_dec(x_43);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_16 = x_10;
goto block_26;
}
block_26:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_9, 2);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_st_ref_set(x_5, x_19, x_11);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_usize_of_nat(x_22);
x_24 = lean_usize_add(x_2, x_23);
x_2 = x_24;
x_4 = x_15;
x_6 = x_21;
goto _start;
}
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_4);
lean_ctor_set(x_70, 1, x_6);
return x_70;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_spec__0___redArg(x_1, x_2, x_3, x_4, x_6, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_getPropHyps(x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_array_get_size(x_11);
x_14 = lean_box(0);
x_15 = lean_nat_dec_lt(x_1, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_13, x_13);
if (x_16 == 0)
{
lean_dec(x_13);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
lean_free_object(x_9);
x_17 = lean_usize_of_nat(x_1);
x_18 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_19 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_spec__0___redArg(x_11, x_17, x_18, x_14, x_3, x_12);
lean_dec(x_11);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_22 = lean_array_get_size(x_20);
x_23 = lean_box(0);
x_24 = lean_nat_dec_lt(x_1, x_22);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_22);
lean_dec(x_20);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_le(x_22, x_22);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_22);
lean_dec(x_20);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_21);
return x_27;
}
else
{
size_t x_28; size_t x_29; lean_object* x_30; 
x_28 = lean_usize_of_nat(x_1);
x_29 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_30 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_spec__0___redArg(x_20, x_28, x_29, x_23, x_3, x_21);
lean_dec(x_20);
return x_30;
}
}
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_9);
if (x_31 == 0)
{
return x_9;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_9, 0);
x_33 = lean_ctor_get(x_9, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_9);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_9 = l_Lean_Elab_Tactic_BVDecide_Frontend_bvNormalizeExt;
x_10 = l_Lean_Meta_SimpExtension_getTheorems___redArg(x_9, x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Tactic_BVDecide_Frontend_bvNormalizeSimprocExt;
x_14 = l_Lean_Meta_Simp_SimprocExtension_getSimprocs___redArg(x_13, x_7, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_getSEvalTheorems(x_6, x_7, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Meta_Simp_getSEvalSimprocs(x_6, x_7, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Meta_getSimpCongrTheorems(x_6, x_7, x_22);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
x_28 = lean_unsigned_to_nat(2u);
x_29 = lean_box(0);
x_30 = lean_box(1);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 20);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_28);
x_33 = lean_unbox(x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2, x_33);
x_34 = lean_unbox(x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 1, x_34);
x_35 = lean_unbox(x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 2, x_35);
x_36 = lean_unbox(x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 3, x_36);
x_37 = lean_unbox(x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 4, x_37);
x_38 = lean_unbox(x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 5, x_38);
x_39 = lean_unbox(x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 6, x_39);
x_40 = lean_unbox(x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 7, x_40);
x_41 = lean_unbox(x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 8, x_41);
x_42 = lean_unbox(x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 9, x_42);
x_43 = lean_unbox(x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 10, x_43);
x_44 = lean_unbox(x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 11, x_44);
x_45 = lean_unbox(x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 12, x_45);
x_46 = lean_unbox(x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 13, x_46);
x_47 = lean_unbox(x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 14, x_47);
x_48 = lean_unbox(x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 15, x_48);
x_49 = lean_unbox(x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_49);
x_50 = lean_unbox(x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 17, x_50);
x_51 = lean_unbox(x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 18, x_51);
x_52 = lean_unbox(x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 19, x_52);
x_53 = lean_mk_empty_array_with_capacity(x_28);
lean_inc(x_53);
x_54 = lean_array_push(x_53, x_11);
x_55 = lean_array_push(x_54, x_18);
x_56 = l_Lean_Meta_Simp_mkContext(x_32, x_55, x_25, x_4, x_5, x_6, x_7, x_26);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_60 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_59);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = lean_ctor_get(x_60, 1);
x_64 = l_Array_isEmpty___redArg(x_62);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; size_t x_73; lean_object* x_74; lean_object* x_75; size_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; 
lean_free_object(x_60);
x_65 = lean_array_push(x_53, x_15);
x_66 = lean_array_push(x_65, x_21);
x_67 = lean_box(0);
x_68 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_68);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = lean_unsigned_to_nat(0u);
lean_inc(x_69);
lean_ctor_set(x_56, 1, x_70);
lean_ctor_set(x_56, 0, x_69);
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_68);
x_72 = lean_unsigned_to_nat(5u);
x_73 = lean_usize_of_nat(x_72);
x_74 = lean_usize_to_nat(x_73);
x_75 = lean_nat_pow(x_28, x_74);
lean_dec(x_74);
x_76 = lean_usize_of_nat(x_75);
lean_dec(x_75);
x_77 = lean_usize_to_nat(x_76);
x_78 = lean_mk_empty_array_with_capacity(x_77);
lean_dec(x_77);
lean_inc(x_78);
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_80 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
lean_ctor_set(x_80, 2, x_70);
lean_ctor_set(x_80, 3, x_70);
lean_ctor_set_usize(x_80, 4, x_73);
lean_inc(x_69);
x_81 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_81, 0, x_69);
lean_ctor_set(x_81, 1, x_69);
lean_ctor_set(x_81, 2, x_71);
lean_ctor_set(x_81, 3, x_80);
lean_ctor_set(x_23, 1, x_81);
lean_ctor_set(x_23, 0, x_56);
x_82 = lean_unbox(x_30);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_83 = l_Lean_Meta_simpGoal(x_1, x_58, x_66, x_67, x_82, x_62, x_23, x_4, x_5, x_6, x_7, x_63);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_dec(x_84);
if (lean_obj_tag(x_85) == 0)
{
uint8_t x_86; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_86 = !lean_is_exclusive(x_83);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_83, 0);
lean_dec(x_87);
x_88 = lean_box(0);
lean_ctor_set(x_83, 0, x_88);
return x_83;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
lean_dec(x_83);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
else
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_85);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_85, 0);
x_94 = lean_ctor_get(x_83, 1);
lean_inc(x_94);
lean_dec(x_83);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__0___boxed), 8, 1);
lean_closure_set(x_96, 0, x_70);
lean_inc(x_95);
x_97 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__2___redArg(x_95, x_96, x_2, x_3, x_4, x_5, x_6, x_7, x_94);
if (lean_obj_tag(x_97) == 0)
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_97, 0);
lean_dec(x_99);
lean_ctor_set(x_85, 0, x_95);
lean_ctor_set(x_97, 0, x_85);
return x_97;
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
lean_ctor_set(x_85, 0, x_95);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_85);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
else
{
uint8_t x_102; 
lean_dec(x_95);
lean_free_object(x_85);
x_102 = !lean_is_exclusive(x_97);
if (x_102 == 0)
{
return x_97;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_97, 0);
x_104 = lean_ctor_get(x_97, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_97);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_106 = lean_ctor_get(x_85, 0);
lean_inc(x_106);
lean_dec(x_85);
x_107 = lean_ctor_get(x_83, 1);
lean_inc(x_107);
lean_dec(x_83);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__0___boxed), 8, 1);
lean_closure_set(x_109, 0, x_70);
lean_inc(x_108);
x_110 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__2___redArg(x_108, x_109, x_2, x_3, x_4, x_5, x_6, x_7, x_107);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_112 = x_110;
} else {
 lean_dec_ref(x_110);
 x_112 = lean_box(0);
}
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_108);
if (lean_is_scalar(x_112)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_112;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_111);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_108);
x_115 = lean_ctor_get(x_110, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_110, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_117 = x_110;
} else {
 lean_dec_ref(x_110);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_119 = !lean_is_exclusive(x_83);
if (x_119 == 0)
{
return x_83;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_83, 0);
x_121 = lean_ctor_get(x_83, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_83);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
lean_object* x_123; 
lean_dec(x_62);
lean_free_object(x_56);
lean_dec(x_58);
lean_dec(x_53);
lean_free_object(x_23);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_1);
lean_ctor_set(x_60, 0, x_123);
return x_60;
}
}
else
{
lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_124 = lean_ctor_get(x_60, 0);
x_125 = lean_ctor_get(x_60, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_60);
x_126 = l_Array_isEmpty___redArg(x_124);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; size_t x_135; lean_object* x_136; lean_object* x_137; size_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; 
x_127 = lean_array_push(x_53, x_15);
x_128 = lean_array_push(x_127, x_21);
x_129 = lean_box(0);
x_130 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_130);
x_131 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_131, 0, x_130);
x_132 = lean_unsigned_to_nat(0u);
lean_inc(x_131);
lean_ctor_set(x_56, 1, x_132);
lean_ctor_set(x_56, 0, x_131);
x_133 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_133, 0, x_130);
x_134 = lean_unsigned_to_nat(5u);
x_135 = lean_usize_of_nat(x_134);
x_136 = lean_usize_to_nat(x_135);
x_137 = lean_nat_pow(x_28, x_136);
lean_dec(x_136);
x_138 = lean_usize_of_nat(x_137);
lean_dec(x_137);
x_139 = lean_usize_to_nat(x_138);
x_140 = lean_mk_empty_array_with_capacity(x_139);
lean_dec(x_139);
lean_inc(x_140);
x_141 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_141, 0, x_140);
x_142 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_140);
lean_ctor_set(x_142, 2, x_132);
lean_ctor_set(x_142, 3, x_132);
lean_ctor_set_usize(x_142, 4, x_135);
lean_inc(x_131);
x_143 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_143, 0, x_131);
lean_ctor_set(x_143, 1, x_131);
lean_ctor_set(x_143, 2, x_133);
lean_ctor_set(x_143, 3, x_142);
lean_ctor_set(x_23, 1, x_143);
lean_ctor_set(x_23, 0, x_56);
x_144 = lean_unbox(x_30);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_145 = l_Lean_Meta_simpGoal(x_1, x_58, x_128, x_129, x_144, x_124, x_23, x_4, x_5, x_6, x_7, x_125);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
lean_dec(x_146);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_148 = lean_ctor_get(x_145, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_149 = x_145;
} else {
 lean_dec_ref(x_145);
 x_149 = lean_box(0);
}
x_150 = lean_box(0);
if (lean_is_scalar(x_149)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_149;
}
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_148);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_152 = lean_ctor_get(x_147, 0);
lean_inc(x_152);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 x_153 = x_147;
} else {
 lean_dec_ref(x_147);
 x_153 = lean_box(0);
}
x_154 = lean_ctor_get(x_145, 1);
lean_inc(x_154);
lean_dec(x_145);
x_155 = lean_ctor_get(x_152, 1);
lean_inc(x_155);
lean_dec(x_152);
x_156 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__0___boxed), 8, 1);
lean_closure_set(x_156, 0, x_132);
lean_inc(x_155);
x_157 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__2___redArg(x_155, x_156, x_2, x_3, x_4, x_5, x_6, x_7, x_154);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_159 = x_157;
} else {
 lean_dec_ref(x_157);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_160 = lean_alloc_ctor(1, 1, 0);
} else {
 x_160 = x_153;
}
lean_ctor_set(x_160, 0, x_155);
if (lean_is_scalar(x_159)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_159;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_158);
return x_161;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_155);
lean_dec(x_153);
x_162 = lean_ctor_get(x_157, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_157, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_164 = x_157;
} else {
 lean_dec_ref(x_157);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_163);
return x_165;
}
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_166 = lean_ctor_get(x_145, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_145, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_168 = x_145;
} else {
 lean_dec_ref(x_145);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
else
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_124);
lean_free_object(x_56);
lean_dec(x_58);
lean_dec(x_53);
lean_free_object(x_23);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_1);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_125);
return x_171;
}
}
}
else
{
uint8_t x_172; 
lean_free_object(x_56);
lean_dec(x_58);
lean_dec(x_53);
lean_free_object(x_23);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_172 = !lean_is_exclusive(x_60);
if (x_172 == 0)
{
return x_60;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_60, 0);
x_174 = lean_ctor_get(x_60, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_60);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_56, 0);
x_177 = lean_ctor_get(x_56, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_56);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_178 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_177);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_181 = x_178;
} else {
 lean_dec_ref(x_178);
 x_181 = lean_box(0);
}
x_182 = l_Array_isEmpty___redArg(x_179);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; size_t x_192; lean_object* x_193; lean_object* x_194; size_t x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; lean_object* x_202; 
lean_dec(x_181);
x_183 = lean_array_push(x_53, x_15);
x_184 = lean_array_push(x_183, x_21);
x_185 = lean_box(0);
x_186 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_186);
x_187 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_187, 0, x_186);
x_188 = lean_unsigned_to_nat(0u);
lean_inc(x_187);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
x_190 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_190, 0, x_186);
x_191 = lean_unsigned_to_nat(5u);
x_192 = lean_usize_of_nat(x_191);
x_193 = lean_usize_to_nat(x_192);
x_194 = lean_nat_pow(x_28, x_193);
lean_dec(x_193);
x_195 = lean_usize_of_nat(x_194);
lean_dec(x_194);
x_196 = lean_usize_to_nat(x_195);
x_197 = lean_mk_empty_array_with_capacity(x_196);
lean_dec(x_196);
lean_inc(x_197);
x_198 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_198, 0, x_197);
x_199 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_197);
lean_ctor_set(x_199, 2, x_188);
lean_ctor_set(x_199, 3, x_188);
lean_ctor_set_usize(x_199, 4, x_192);
lean_inc(x_187);
x_200 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_200, 0, x_187);
lean_ctor_set(x_200, 1, x_187);
lean_ctor_set(x_200, 2, x_190);
lean_ctor_set(x_200, 3, x_199);
lean_ctor_set(x_23, 1, x_200);
lean_ctor_set(x_23, 0, x_189);
x_201 = lean_unbox(x_30);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_202 = l_Lean_Meta_simpGoal(x_1, x_176, x_184, x_185, x_201, x_179, x_23, x_4, x_5, x_6, x_7, x_180);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
lean_dec(x_203);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_205 = lean_ctor_get(x_202, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_206 = x_202;
} else {
 lean_dec_ref(x_202);
 x_206 = lean_box(0);
}
x_207 = lean_box(0);
if (lean_is_scalar(x_206)) {
 x_208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_208 = x_206;
}
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_205);
return x_208;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_209 = lean_ctor_get(x_204, 0);
lean_inc(x_209);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 x_210 = x_204;
} else {
 lean_dec_ref(x_204);
 x_210 = lean_box(0);
}
x_211 = lean_ctor_get(x_202, 1);
lean_inc(x_211);
lean_dec(x_202);
x_212 = lean_ctor_get(x_209, 1);
lean_inc(x_212);
lean_dec(x_209);
x_213 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__0___boxed), 8, 1);
lean_closure_set(x_213, 0, x_188);
lean_inc(x_212);
x_214 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__2___redArg(x_212, x_213, x_2, x_3, x_4, x_5, x_6, x_7, x_211);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_215 = lean_ctor_get(x_214, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_216 = x_214;
} else {
 lean_dec_ref(x_214);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_210)) {
 x_217 = lean_alloc_ctor(1, 1, 0);
} else {
 x_217 = x_210;
}
lean_ctor_set(x_217, 0, x_212);
if (lean_is_scalar(x_216)) {
 x_218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_218 = x_216;
}
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_215);
return x_218;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_dec(x_212);
lean_dec(x_210);
x_219 = lean_ctor_get(x_214, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_214, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_221 = x_214;
} else {
 lean_dec_ref(x_214);
 x_221 = lean_box(0);
}
if (lean_is_scalar(x_221)) {
 x_222 = lean_alloc_ctor(1, 2, 0);
} else {
 x_222 = x_221;
}
lean_ctor_set(x_222, 0, x_219);
lean_ctor_set(x_222, 1, x_220);
return x_222;
}
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_223 = lean_ctor_get(x_202, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_202, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_225 = x_202;
} else {
 lean_dec_ref(x_202);
 x_225 = lean_box(0);
}
if (lean_is_scalar(x_225)) {
 x_226 = lean_alloc_ctor(1, 2, 0);
} else {
 x_226 = x_225;
}
lean_ctor_set(x_226, 0, x_223);
lean_ctor_set(x_226, 1, x_224);
return x_226;
}
}
else
{
lean_object* x_227; lean_object* x_228; 
lean_dec(x_179);
lean_dec(x_176);
lean_dec(x_53);
lean_free_object(x_23);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_227 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_227, 0, x_1);
if (lean_is_scalar(x_181)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_181;
}
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_180);
return x_228;
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_176);
lean_dec(x_53);
lean_free_object(x_23);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_229 = lean_ctor_get(x_178, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_178, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_231 = x_178;
} else {
 lean_dec_ref(x_178);
 x_231 = lean_box(0);
}
if (lean_is_scalar(x_231)) {
 x_232 = lean_alloc_ctor(1, 2, 0);
} else {
 x_232 = x_231;
}
lean_ctor_set(x_232, 0, x_229);
lean_ctor_set(x_232, 1, x_230);
return x_232;
}
}
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; uint8_t x_242; uint8_t x_243; uint8_t x_244; uint8_t x_245; uint8_t x_246; uint8_t x_247; uint8_t x_248; uint8_t x_249; uint8_t x_250; uint8_t x_251; uint8_t x_252; uint8_t x_253; uint8_t x_254; uint8_t x_255; uint8_t x_256; uint8_t x_257; uint8_t x_258; uint8_t x_259; uint8_t x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_233 = lean_ctor_get(x_23, 0);
x_234 = lean_ctor_get(x_23, 1);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_23);
x_235 = lean_ctor_get(x_2, 1);
lean_inc(x_235);
x_236 = lean_unsigned_to_nat(2u);
x_237 = lean_box(0);
x_238 = lean_box(1);
x_239 = lean_box(0);
x_240 = lean_alloc_ctor(0, 2, 20);
lean_ctor_set(x_240, 0, x_235);
lean_ctor_set(x_240, 1, x_236);
x_241 = lean_unbox(x_237);
lean_ctor_set_uint8(x_240, sizeof(void*)*2, x_241);
x_242 = lean_unbox(x_238);
lean_ctor_set_uint8(x_240, sizeof(void*)*2 + 1, x_242);
x_243 = lean_unbox(x_237);
lean_ctor_set_uint8(x_240, sizeof(void*)*2 + 2, x_243);
x_244 = lean_unbox(x_238);
lean_ctor_set_uint8(x_240, sizeof(void*)*2 + 3, x_244);
x_245 = lean_unbox(x_238);
lean_ctor_set_uint8(x_240, sizeof(void*)*2 + 4, x_245);
x_246 = lean_unbox(x_238);
lean_ctor_set_uint8(x_240, sizeof(void*)*2 + 5, x_246);
x_247 = lean_unbox(x_239);
lean_ctor_set_uint8(x_240, sizeof(void*)*2 + 6, x_247);
x_248 = lean_unbox(x_238);
lean_ctor_set_uint8(x_240, sizeof(void*)*2 + 7, x_248);
x_249 = lean_unbox(x_238);
lean_ctor_set_uint8(x_240, sizeof(void*)*2 + 8, x_249);
x_250 = lean_unbox(x_237);
lean_ctor_set_uint8(x_240, sizeof(void*)*2 + 9, x_250);
x_251 = lean_unbox(x_237);
lean_ctor_set_uint8(x_240, sizeof(void*)*2 + 10, x_251);
x_252 = lean_unbox(x_237);
lean_ctor_set_uint8(x_240, sizeof(void*)*2 + 11, x_252);
x_253 = lean_unbox(x_238);
lean_ctor_set_uint8(x_240, sizeof(void*)*2 + 12, x_253);
x_254 = lean_unbox(x_237);
lean_ctor_set_uint8(x_240, sizeof(void*)*2 + 13, x_254);
x_255 = lean_unbox(x_237);
lean_ctor_set_uint8(x_240, sizeof(void*)*2 + 14, x_255);
x_256 = lean_unbox(x_237);
lean_ctor_set_uint8(x_240, sizeof(void*)*2 + 15, x_256);
x_257 = lean_unbox(x_238);
lean_ctor_set_uint8(x_240, sizeof(void*)*2 + 16, x_257);
x_258 = lean_unbox(x_238);
lean_ctor_set_uint8(x_240, sizeof(void*)*2 + 17, x_258);
x_259 = lean_unbox(x_237);
lean_ctor_set_uint8(x_240, sizeof(void*)*2 + 18, x_259);
x_260 = lean_unbox(x_238);
lean_ctor_set_uint8(x_240, sizeof(void*)*2 + 19, x_260);
x_261 = lean_mk_empty_array_with_capacity(x_236);
lean_inc(x_261);
x_262 = lean_array_push(x_261, x_11);
x_263 = lean_array_push(x_262, x_18);
x_264 = l_Lean_Meta_Simp_mkContext(x_240, x_263, x_233, x_4, x_5, x_6, x_7, x_234);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 x_267 = x_264;
} else {
 lean_dec_ref(x_264);
 x_267 = lean_box(0);
}
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_268 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_266);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; 
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 x_271 = x_268;
} else {
 lean_dec_ref(x_268);
 x_271 = lean_box(0);
}
x_272 = l_Array_isEmpty___redArg(x_269);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; size_t x_282; lean_object* x_283; lean_object* x_284; size_t x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; lean_object* x_293; 
lean_dec(x_271);
x_273 = lean_array_push(x_261, x_15);
x_274 = lean_array_push(x_273, x_21);
x_275 = lean_box(0);
x_276 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_276);
x_277 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_277, 0, x_276);
x_278 = lean_unsigned_to_nat(0u);
lean_inc(x_277);
if (lean_is_scalar(x_267)) {
 x_279 = lean_alloc_ctor(0, 2, 0);
} else {
 x_279 = x_267;
}
lean_ctor_set(x_279, 0, x_277);
lean_ctor_set(x_279, 1, x_278);
x_280 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_280, 0, x_276);
x_281 = lean_unsigned_to_nat(5u);
x_282 = lean_usize_of_nat(x_281);
x_283 = lean_usize_to_nat(x_282);
x_284 = lean_nat_pow(x_236, x_283);
lean_dec(x_283);
x_285 = lean_usize_of_nat(x_284);
lean_dec(x_284);
x_286 = lean_usize_to_nat(x_285);
x_287 = lean_mk_empty_array_with_capacity(x_286);
lean_dec(x_286);
lean_inc(x_287);
x_288 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_288, 0, x_287);
x_289 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_287);
lean_ctor_set(x_289, 2, x_278);
lean_ctor_set(x_289, 3, x_278);
lean_ctor_set_usize(x_289, 4, x_282);
lean_inc(x_277);
x_290 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_290, 0, x_277);
lean_ctor_set(x_290, 1, x_277);
lean_ctor_set(x_290, 2, x_280);
lean_ctor_set(x_290, 3, x_289);
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_279);
lean_ctor_set(x_291, 1, x_290);
x_292 = lean_unbox(x_238);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_293 = l_Lean_Meta_simpGoal(x_1, x_265, x_274, x_275, x_292, x_269, x_291, x_4, x_5, x_6, x_7, x_270);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; 
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
lean_dec(x_294);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_296 = lean_ctor_get(x_293, 1);
lean_inc(x_296);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 x_297 = x_293;
} else {
 lean_dec_ref(x_293);
 x_297 = lean_box(0);
}
x_298 = lean_box(0);
if (lean_is_scalar(x_297)) {
 x_299 = lean_alloc_ctor(0, 2, 0);
} else {
 x_299 = x_297;
}
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_296);
return x_299;
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_300 = lean_ctor_get(x_295, 0);
lean_inc(x_300);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 x_301 = x_295;
} else {
 lean_dec_ref(x_295);
 x_301 = lean_box(0);
}
x_302 = lean_ctor_get(x_293, 1);
lean_inc(x_302);
lean_dec(x_293);
x_303 = lean_ctor_get(x_300, 1);
lean_inc(x_303);
lean_dec(x_300);
x_304 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__0___boxed), 8, 1);
lean_closure_set(x_304, 0, x_278);
lean_inc(x_303);
x_305 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__2___redArg(x_303, x_304, x_2, x_3, x_4, x_5, x_6, x_7, x_302);
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_306 = lean_ctor_get(x_305, 1);
lean_inc(x_306);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 lean_ctor_release(x_305, 1);
 x_307 = x_305;
} else {
 lean_dec_ref(x_305);
 x_307 = lean_box(0);
}
if (lean_is_scalar(x_301)) {
 x_308 = lean_alloc_ctor(1, 1, 0);
} else {
 x_308 = x_301;
}
lean_ctor_set(x_308, 0, x_303);
if (lean_is_scalar(x_307)) {
 x_309 = lean_alloc_ctor(0, 2, 0);
} else {
 x_309 = x_307;
}
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_306);
return x_309;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_dec(x_303);
lean_dec(x_301);
x_310 = lean_ctor_get(x_305, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_305, 1);
lean_inc(x_311);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 lean_ctor_release(x_305, 1);
 x_312 = x_305;
} else {
 lean_dec_ref(x_305);
 x_312 = lean_box(0);
}
if (lean_is_scalar(x_312)) {
 x_313 = lean_alloc_ctor(1, 2, 0);
} else {
 x_313 = x_312;
}
lean_ctor_set(x_313, 0, x_310);
lean_ctor_set(x_313, 1, x_311);
return x_313;
}
}
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_314 = lean_ctor_get(x_293, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_293, 1);
lean_inc(x_315);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 x_316 = x_293;
} else {
 lean_dec_ref(x_293);
 x_316 = lean_box(0);
}
if (lean_is_scalar(x_316)) {
 x_317 = lean_alloc_ctor(1, 2, 0);
} else {
 x_317 = x_316;
}
lean_ctor_set(x_317, 0, x_314);
lean_ctor_set(x_317, 1, x_315);
return x_317;
}
}
else
{
lean_object* x_318; lean_object* x_319; 
lean_dec(x_269);
lean_dec(x_267);
lean_dec(x_265);
lean_dec(x_261);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_318 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_318, 0, x_1);
if (lean_is_scalar(x_271)) {
 x_319 = lean_alloc_ctor(0, 2, 0);
} else {
 x_319 = x_271;
}
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_319, 1, x_270);
return x_319;
}
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
lean_dec(x_267);
lean_dec(x_265);
lean_dec(x_261);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_320 = lean_ctor_get(x_268, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_268, 1);
lean_inc(x_321);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 x_322 = x_268;
} else {
 lean_dec_ref(x_268);
 x_322 = lean_box(0);
}
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(1, 2, 0);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_320);
lean_ctor_set(x_323, 1, x_321);
return x_323;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___boxed), 8, 0);
x_2 = lean_mk_string_unchecked("rewriteRules", 12, 12);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_spec__0___redArg(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_spec__0(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
lean_object* initialize_Lean_Elab_Tactic_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Attr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Rewrite(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_Attr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
