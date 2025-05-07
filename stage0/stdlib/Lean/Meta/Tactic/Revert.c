// Lean compiler output
// Module: Lean.Meta.Tactic.Revert
// Imports: Lean.Meta.Tactic.Clear
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t l_Array_isEmpty___redArg(lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAfter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_MVarId_revert_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0_spec__0_spec__0_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_setKind(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_MVarId_revert_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_MVarId_revert_spec__2_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_MVarId_revert_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAfter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0_spec__0_spec__0_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_MVarId_revert_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_MVarId_revert_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_collectForwardDeps(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_revert(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_MVarId_revert_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0_spec__0_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_setTag___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___Lean_LocalContext_getFVars_spec__0(size_t, size_t, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_MVarId_revert_spec__1___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAfter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_MetavarContext_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_MVarId_revert_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_3, x_2);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_array_uget(x_1, x_3);
x_20 = l_Lean_Expr_fvarId_x21(x_19);
lean_inc(x_5);
lean_inc(x_20);
x_21 = l_Lean_FVarId_getDecl___redArg(x_20, x_5, x_7, x_8, x_9);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_4, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_4, 1);
lean_inc(x_25);
lean_dec(x_4);
x_26 = l_Lean_LocalDecl_isAuxDecl(x_22);
lean_dec(x_22);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_20);
x_27 = lean_array_push(x_25, x_19);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_27);
x_10 = x_28;
x_11 = x_23;
goto block_16;
}
else
{
lean_object* x_29; 
lean_dec(x_19);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_29 = l_Lean_MVarId_clear(x_24, x_20, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_25);
x_10 = x_32;
x_11 = x_31;
goto block_16;
}
else
{
uint8_t x_33; 
lean_dec(x_25);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
}
else
{
uint8_t x_37; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_37 = !lean_is_exclusive(x_21);
if (x_37 == 0)
{
return x_21;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_21, 0);
x_39 = lean_ctor_get(x_21, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_21);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_MVarId_revert_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = l_Lean_Expr_fvarId_x21(x_5);
lean_dec(x_5);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_MVarId_revert_spec__2_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_3, x_2);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
x_19 = lean_array_uget(x_1, x_3);
lean_inc(x_5);
lean_inc(x_19);
x_20 = l_Lean_FVarId_getDecl___redArg(x_19, x_5, x_7, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = l_Lean_LocalDecl_isAuxDecl(x_21);
lean_dec(x_21);
if (x_24 == 0)
{
lean_dec(x_19);
x_10 = x_23;
x_11 = x_22;
goto block_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_mk_string_unchecked("failed to revert ", 17, 17);
x_26 = l_Lean_stringToMessageData(x_25);
lean_dec(x_25);
x_27 = l_Lean_Expr_fvar___override(x_19);
x_28 = l_Lean_MessageData_ofExpr(x_27);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_mk_string_unchecked(", it is an auxiliary declaration created to represent recursive definitions", 75, 75);
x_31 = l_Lean_stringToMessageData(x_30);
lean_dec(x_30);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_32, x_5, x_6, x_7, x_8, x_22);
lean_dec(x_5);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_19);
lean_dec(x_5);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
return x_20;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_20, 0);
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_20);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_MVarId_revert_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_3, x_2);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
x_19 = lean_array_uget(x_1, x_3);
lean_inc(x_5);
lean_inc(x_19);
x_20 = l_Lean_FVarId_getDecl___redArg(x_19, x_5, x_7, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = l_Lean_LocalDecl_isAuxDecl(x_21);
lean_dec(x_21);
if (x_24 == 0)
{
lean_dec(x_19);
x_10 = x_23;
x_11 = x_22;
goto block_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_mk_string_unchecked("failed to revert ", 17, 17);
x_26 = l_Lean_stringToMessageData(x_25);
lean_dec(x_25);
x_27 = l_Lean_Expr_fvar___override(x_19);
x_28 = l_Lean_MessageData_ofExpr(x_27);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_mk_string_unchecked(", it is an auxiliary declaration created to represent recursive definitions", 75, 75);
x_31 = l_Lean_stringToMessageData(x_30);
lean_dec(x_30);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_32, x_5, x_6, x_7, x_8, x_22);
lean_dec(x_5);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_19);
lean_dec(x_5);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
return x_20;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_20, 0);
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_20);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
block_16:
{
lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_3, x_13);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_MVarId_revert_spec__2_spec__2(x_1, x_2, x_14, x_10, x_5, x_6, x_7, x_8, x_11);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_387; 
lean_inc(x_1);
x_387 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_387) == 0)
{
if (x_5 == 0)
{
lean_object* x_388; lean_object* x_389; size_t x_390; lean_object* x_391; size_t x_392; lean_object* x_393; 
x_388 = lean_ctor_get(x_387, 1);
lean_inc(x_388);
lean_dec(x_387);
x_389 = lean_box(0);
x_390 = lean_array_size(x_3);
x_391 = lean_unsigned_to_nat(0u);
x_392 = lean_usize_of_nat(x_391);
lean_inc(x_6);
x_393 = l_Array_forIn_x27Unsafe_loop___at___Lean_MVarId_revert_spec__2(x_3, x_390, x_392, x_389, x_6, x_7, x_8, x_9, x_388);
if (lean_obj_tag(x_393) == 0)
{
lean_object* x_394; 
x_394 = lean_ctor_get(x_393, 1);
lean_inc(x_394);
lean_dec(x_393);
x_11 = x_6;
x_12 = x_7;
x_13 = x_8;
x_14 = x_9;
x_15 = x_394;
goto block_386;
}
else
{
uint8_t x_395; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_395 = !lean_is_exclusive(x_393);
if (x_395 == 0)
{
return x_393;
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_396 = lean_ctor_get(x_393, 0);
x_397 = lean_ctor_get(x_393, 1);
lean_inc(x_397);
lean_inc(x_396);
lean_dec(x_393);
x_398 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_398, 0, x_396);
lean_ctor_set(x_398, 1, x_397);
return x_398;
}
}
}
else
{
lean_object* x_399; 
x_399 = lean_ctor_get(x_387, 1);
lean_inc(x_399);
lean_dec(x_387);
x_11 = x_6;
x_12 = x_7;
x_13 = x_8;
x_14 = x_9;
x_15 = x_399;
goto block_386;
}
}
else
{
uint8_t x_400; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_400 = !lean_is_exclusive(x_387);
if (x_400 == 0)
{
return x_387;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_401 = lean_ctor_get(x_387, 0);
x_402 = lean_ctor_get(x_387, 1);
lean_inc(x_402);
lean_inc(x_401);
lean_dec(x_387);
x_403 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_403, 0, x_401);
lean_ctor_set(x_403, 1, x_402);
return x_403;
}
}
block_386:
{
size_t x_16; lean_object* x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_size(x_3);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_usize_of_nat(x_17);
x_19 = l_Array_mapMUnsafe_map___at___Lean_LocalContext_getFVars_spec__0(x_16, x_18, x_3);
lean_inc(x_11);
x_20 = l_Lean_Meta_collectForwardDeps(x_19, x_4, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_mk_empty_array_with_capacity(x_17);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_array_size(x_21);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_26 = l_Array_forIn_x27Unsafe_loop___at___Lean_MVarId_revert_spec__0(x_21, x_25, x_18, x_24, x_11, x_12, x_13, x_14, x_22);
lean_dec(x_21);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
lean_inc(x_29);
x_31 = l_Lean_MVarId_getTag(x_29, x_11, x_12, x_13, x_14, x_28);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_box(0);
x_35 = lean_unbox(x_34);
lean_inc(x_29);
x_36 = l_Lean_MVarId_setKind(x_29, x_35, x_11, x_12, x_13, x_14, x_33);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_st_ref_get(x_14, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_st_ref_get(x_12, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_st_ref_get(x_14, x_43);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_ctor_get(x_44, 1);
x_48 = lean_st_ref_get(x_14, x_47);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_48, 1);
x_52 = lean_box(2);
x_53 = lean_ctor_get(x_11, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_39, 0);
lean_inc(x_54);
lean_dec(x_39);
x_55 = lean_ctor_get(x_42, 0);
lean_inc(x_55);
lean_dec(x_42);
x_56 = lean_ctor_get(x_46, 2);
lean_inc(x_56);
lean_dec(x_46);
x_57 = l_Lean_Environment_mainModule(x_54);
lean_dec(x_54);
lean_ctor_set(x_48, 1, x_53);
lean_ctor_set(x_48, 0, x_57);
x_58 = lean_ctor_get(x_50, 1);
lean_inc(x_58);
lean_dec(x_50);
x_59 = lean_unsigned_to_nat(8u);
x_60 = lean_unsigned_to_nat(2u);
x_61 = lean_nat_shiftl(x_59, x_60);
x_62 = lean_unsigned_to_nat(3u);
x_63 = lean_nat_div(x_61, x_62);
lean_dec(x_61);
x_64 = l_Nat_nextPowerOfTwo(x_63);
lean_dec(x_63);
x_65 = lean_box(0);
x_66 = lean_mk_array(x_64, x_65);
lean_ctor_set(x_44, 1, x_66);
lean_ctor_set(x_44, 0, x_17);
x_67 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_67, 0, x_55);
lean_ctor_set(x_67, 1, x_58);
lean_ctor_set(x_67, 2, x_56);
lean_ctor_set(x_67, 3, x_44);
lean_inc(x_29);
x_68 = l_Lean_MetavarContext_revert(x_30, x_29, x_4, x_48, x_67);
lean_dec(x_67);
lean_dec(x_48);
lean_dec(x_30);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_st_ref_take(x_12, x_51);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_ctor_get(x_70, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_72, 2);
lean_inc(x_76);
x_77 = lean_ctor_get(x_72, 3);
lean_inc(x_77);
x_78 = lean_ctor_get(x_72, 4);
lean_inc(x_78);
lean_dec(x_72);
x_79 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_79, 0, x_74);
lean_ctor_set(x_79, 1, x_75);
lean_ctor_set(x_79, 2, x_76);
lean_ctor_set(x_79, 3, x_77);
lean_ctor_set(x_79, 4, x_78);
x_80 = lean_st_ref_set(x_12, x_79, x_73);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = lean_st_ref_take(x_14, x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_ctor_get(x_83, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_70, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_70, 2);
lean_inc(x_87);
lean_dec(x_70);
x_88 = lean_ctor_get(x_83, 3);
lean_inc(x_88);
x_89 = lean_ctor_get(x_83, 4);
lean_inc(x_89);
x_90 = lean_ctor_get(x_83, 5);
lean_inc(x_90);
x_91 = lean_ctor_get(x_83, 6);
lean_inc(x_91);
x_92 = lean_ctor_get(x_83, 7);
lean_inc(x_92);
lean_dec(x_83);
x_93 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_93, 0, x_85);
lean_ctor_set(x_93, 1, x_86);
lean_ctor_set(x_93, 2, x_87);
lean_ctor_set(x_93, 3, x_88);
lean_ctor_set(x_93, 4, x_89);
lean_ctor_set(x_93, 5, x_90);
lean_ctor_set(x_93, 6, x_91);
lean_ctor_set(x_93, 7, x_92);
x_94 = lean_st_ref_set(x_14, x_93, x_84);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_96 = lean_unbox(x_52);
x_97 = l_Lean_MVarId_setKind(x_29, x_96, x_11, x_12, x_13, x_14, x_95);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_99 = !lean_is_exclusive(x_69);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_100 = lean_ctor_get(x_69, 0);
x_101 = lean_ctor_get(x_69, 1);
x_102 = l_Lean_Expr_getAppFn(x_100);
lean_dec(x_100);
x_103 = l_Lean_Expr_mvarId_x21(x_102);
lean_dec(x_102);
x_104 = lean_unbox(x_52);
lean_inc(x_103);
x_105 = l_Lean_MVarId_setKind(x_103, x_104, x_11, x_12, x_13, x_14, x_98);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
lean_inc(x_103);
x_107 = l_Lean_MVarId_setTag___redArg(x_103, x_32, x_12, x_106);
lean_dec(x_12);
x_108 = !lean_is_exclusive(x_107);
if (x_108 == 0)
{
lean_object* x_109; size_t x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_107, 0);
lean_dec(x_109);
x_110 = lean_array_size(x_101);
x_111 = l_Array_mapMUnsafe_map___at___Lean_MVarId_revert_spec__1(x_110, x_18, x_101);
lean_ctor_set(x_69, 1, x_103);
lean_ctor_set(x_69, 0, x_111);
lean_ctor_set(x_107, 0, x_69);
return x_107;
}
else
{
lean_object* x_112; size_t x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_107, 1);
lean_inc(x_112);
lean_dec(x_107);
x_113 = lean_array_size(x_101);
x_114 = l_Array_mapMUnsafe_map___at___Lean_MVarId_revert_spec__1(x_113, x_18, x_101);
lean_ctor_set(x_69, 1, x_103);
lean_ctor_set(x_69, 0, x_114);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_69);
lean_ctor_set(x_115, 1, x_112);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; size_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_116 = lean_ctor_get(x_69, 0);
x_117 = lean_ctor_get(x_69, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_69);
x_118 = l_Lean_Expr_getAppFn(x_116);
lean_dec(x_116);
x_119 = l_Lean_Expr_mvarId_x21(x_118);
lean_dec(x_118);
x_120 = lean_unbox(x_52);
lean_inc(x_119);
x_121 = l_Lean_MVarId_setKind(x_119, x_120, x_11, x_12, x_13, x_14, x_98);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
lean_dec(x_121);
lean_inc(x_119);
x_123 = l_Lean_MVarId_setTag___redArg(x_119, x_32, x_12, x_122);
lean_dec(x_12);
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_125 = x_123;
} else {
 lean_dec_ref(x_123);
 x_125 = lean_box(0);
}
x_126 = lean_array_size(x_117);
x_127 = l_Array_mapMUnsafe_map___at___Lean_MVarId_revert_spec__1(x_126, x_18, x_117);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_119);
if (lean_is_scalar(x_125)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_125;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_124);
return x_129;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; uint8_t x_163; 
lean_dec(x_32);
x_130 = lean_ctor_get(x_68, 1);
lean_inc(x_130);
lean_dec(x_68);
x_131 = lean_st_ref_take(x_12, x_51);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = lean_ctor_get(x_130, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_132, 1);
lean_inc(x_135);
x_136 = lean_ctor_get(x_132, 2);
lean_inc(x_136);
x_137 = lean_ctor_get(x_132, 3);
lean_inc(x_137);
x_138 = lean_ctor_get(x_132, 4);
lean_inc(x_138);
lean_dec(x_132);
x_139 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_139, 0, x_134);
lean_ctor_set(x_139, 1, x_135);
lean_ctor_set(x_139, 2, x_136);
lean_ctor_set(x_139, 3, x_137);
lean_ctor_set(x_139, 4, x_138);
x_140 = lean_st_ref_set(x_12, x_139, x_133);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec(x_140);
x_142 = lean_st_ref_take(x_14, x_141);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = lean_ctor_get(x_143, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_130, 1);
lean_inc(x_146);
x_147 = lean_ctor_get(x_130, 2);
lean_inc(x_147);
lean_dec(x_130);
x_148 = lean_ctor_get(x_143, 3);
lean_inc(x_148);
x_149 = lean_ctor_get(x_143, 4);
lean_inc(x_149);
x_150 = lean_ctor_get(x_143, 5);
lean_inc(x_150);
x_151 = lean_ctor_get(x_143, 6);
lean_inc(x_151);
x_152 = lean_ctor_get(x_143, 7);
lean_inc(x_152);
lean_dec(x_143);
x_153 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_153, 0, x_145);
lean_ctor_set(x_153, 1, x_146);
lean_ctor_set(x_153, 2, x_147);
lean_ctor_set(x_153, 3, x_148);
lean_ctor_set(x_153, 4, x_149);
lean_ctor_set(x_153, 5, x_150);
lean_ctor_set(x_153, 6, x_151);
lean_ctor_set(x_153, 7, x_152);
x_154 = lean_st_ref_set(x_14, x_153, x_144);
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
lean_dec(x_154);
x_156 = lean_mk_string_unchecked("failed to create binder due to failure when reverting variable dependencies", 75, 75);
x_157 = l_Lean_stringToMessageData(x_156);
lean_dec(x_156);
x_158 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_157, x_11, x_12, x_13, x_14, x_155);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = lean_unbox(x_52);
x_162 = l_Lean_MVarId_setKind(x_29, x_161, x_11, x_12, x_13, x_14, x_160);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_163 = !lean_is_exclusive(x_162);
if (x_163 == 0)
{
lean_object* x_164; 
x_164 = lean_ctor_get(x_162, 0);
lean_dec(x_164);
lean_ctor_set_tag(x_162, 1);
lean_ctor_set(x_162, 0, x_159);
return x_162;
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_162, 1);
lean_inc(x_165);
lean_dec(x_162);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_159);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_167 = lean_ctor_get(x_48, 0);
x_168 = lean_ctor_get(x_48, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_48);
x_169 = lean_box(2);
x_170 = lean_ctor_get(x_11, 2);
lean_inc(x_170);
x_171 = lean_ctor_get(x_39, 0);
lean_inc(x_171);
lean_dec(x_39);
x_172 = lean_ctor_get(x_42, 0);
lean_inc(x_172);
lean_dec(x_42);
x_173 = lean_ctor_get(x_46, 2);
lean_inc(x_173);
lean_dec(x_46);
x_174 = l_Lean_Environment_mainModule(x_171);
lean_dec(x_171);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_170);
x_176 = lean_ctor_get(x_167, 1);
lean_inc(x_176);
lean_dec(x_167);
x_177 = lean_unsigned_to_nat(8u);
x_178 = lean_unsigned_to_nat(2u);
x_179 = lean_nat_shiftl(x_177, x_178);
x_180 = lean_unsigned_to_nat(3u);
x_181 = lean_nat_div(x_179, x_180);
lean_dec(x_179);
x_182 = l_Nat_nextPowerOfTwo(x_181);
lean_dec(x_181);
x_183 = lean_box(0);
x_184 = lean_mk_array(x_182, x_183);
lean_ctor_set(x_44, 1, x_184);
lean_ctor_set(x_44, 0, x_17);
x_185 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_185, 0, x_172);
lean_ctor_set(x_185, 1, x_176);
lean_ctor_set(x_185, 2, x_173);
lean_ctor_set(x_185, 3, x_44);
lean_inc(x_29);
x_186 = l_Lean_MetavarContext_revert(x_30, x_29, x_4, x_175, x_185);
lean_dec(x_185);
lean_dec(x_175);
lean_dec(x_30);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; size_t x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
x_189 = lean_st_ref_take(x_12, x_168);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
x_192 = lean_ctor_get(x_188, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_190, 1);
lean_inc(x_193);
x_194 = lean_ctor_get(x_190, 2);
lean_inc(x_194);
x_195 = lean_ctor_get(x_190, 3);
lean_inc(x_195);
x_196 = lean_ctor_get(x_190, 4);
lean_inc(x_196);
lean_dec(x_190);
x_197 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_197, 0, x_192);
lean_ctor_set(x_197, 1, x_193);
lean_ctor_set(x_197, 2, x_194);
lean_ctor_set(x_197, 3, x_195);
lean_ctor_set(x_197, 4, x_196);
x_198 = lean_st_ref_set(x_12, x_197, x_191);
x_199 = lean_ctor_get(x_198, 1);
lean_inc(x_199);
lean_dec(x_198);
x_200 = lean_st_ref_take(x_14, x_199);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
x_203 = lean_ctor_get(x_201, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_188, 1);
lean_inc(x_204);
x_205 = lean_ctor_get(x_188, 2);
lean_inc(x_205);
lean_dec(x_188);
x_206 = lean_ctor_get(x_201, 3);
lean_inc(x_206);
x_207 = lean_ctor_get(x_201, 4);
lean_inc(x_207);
x_208 = lean_ctor_get(x_201, 5);
lean_inc(x_208);
x_209 = lean_ctor_get(x_201, 6);
lean_inc(x_209);
x_210 = lean_ctor_get(x_201, 7);
lean_inc(x_210);
lean_dec(x_201);
x_211 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_211, 0, x_203);
lean_ctor_set(x_211, 1, x_204);
lean_ctor_set(x_211, 2, x_205);
lean_ctor_set(x_211, 3, x_206);
lean_ctor_set(x_211, 4, x_207);
lean_ctor_set(x_211, 5, x_208);
lean_ctor_set(x_211, 6, x_209);
lean_ctor_set(x_211, 7, x_210);
x_212 = lean_st_ref_set(x_14, x_211, x_202);
x_213 = lean_ctor_get(x_212, 1);
lean_inc(x_213);
lean_dec(x_212);
x_214 = lean_unbox(x_169);
x_215 = l_Lean_MVarId_setKind(x_29, x_214, x_11, x_12, x_13, x_14, x_213);
x_216 = lean_ctor_get(x_215, 1);
lean_inc(x_216);
lean_dec(x_215);
x_217 = lean_ctor_get(x_187, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_187, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_219 = x_187;
} else {
 lean_dec_ref(x_187);
 x_219 = lean_box(0);
}
x_220 = l_Lean_Expr_getAppFn(x_217);
lean_dec(x_217);
x_221 = l_Lean_Expr_mvarId_x21(x_220);
lean_dec(x_220);
x_222 = lean_unbox(x_169);
lean_inc(x_221);
x_223 = l_Lean_MVarId_setKind(x_221, x_222, x_11, x_12, x_13, x_14, x_216);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
x_224 = lean_ctor_get(x_223, 1);
lean_inc(x_224);
lean_dec(x_223);
lean_inc(x_221);
x_225 = l_Lean_MVarId_setTag___redArg(x_221, x_32, x_12, x_224);
lean_dec(x_12);
x_226 = lean_ctor_get(x_225, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 x_227 = x_225;
} else {
 lean_dec_ref(x_225);
 x_227 = lean_box(0);
}
x_228 = lean_array_size(x_218);
x_229 = l_Array_mapMUnsafe_map___at___Lean_MVarId_revert_spec__1(x_228, x_18, x_218);
if (lean_is_scalar(x_219)) {
 x_230 = lean_alloc_ctor(0, 2, 0);
} else {
 x_230 = x_219;
}
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_221);
if (lean_is_scalar(x_227)) {
 x_231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_231 = x_227;
}
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_226);
return x_231;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_32);
x_232 = lean_ctor_get(x_186, 1);
lean_inc(x_232);
lean_dec(x_186);
x_233 = lean_st_ref_take(x_12, x_168);
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_236 = lean_ctor_get(x_232, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_234, 1);
lean_inc(x_237);
x_238 = lean_ctor_get(x_234, 2);
lean_inc(x_238);
x_239 = lean_ctor_get(x_234, 3);
lean_inc(x_239);
x_240 = lean_ctor_get(x_234, 4);
lean_inc(x_240);
lean_dec(x_234);
x_241 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_241, 0, x_236);
lean_ctor_set(x_241, 1, x_237);
lean_ctor_set(x_241, 2, x_238);
lean_ctor_set(x_241, 3, x_239);
lean_ctor_set(x_241, 4, x_240);
x_242 = lean_st_ref_set(x_12, x_241, x_235);
x_243 = lean_ctor_get(x_242, 1);
lean_inc(x_243);
lean_dec(x_242);
x_244 = lean_st_ref_take(x_14, x_243);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_247 = lean_ctor_get(x_245, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_232, 1);
lean_inc(x_248);
x_249 = lean_ctor_get(x_232, 2);
lean_inc(x_249);
lean_dec(x_232);
x_250 = lean_ctor_get(x_245, 3);
lean_inc(x_250);
x_251 = lean_ctor_get(x_245, 4);
lean_inc(x_251);
x_252 = lean_ctor_get(x_245, 5);
lean_inc(x_252);
x_253 = lean_ctor_get(x_245, 6);
lean_inc(x_253);
x_254 = lean_ctor_get(x_245, 7);
lean_inc(x_254);
lean_dec(x_245);
x_255 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_255, 0, x_247);
lean_ctor_set(x_255, 1, x_248);
lean_ctor_set(x_255, 2, x_249);
lean_ctor_set(x_255, 3, x_250);
lean_ctor_set(x_255, 4, x_251);
lean_ctor_set(x_255, 5, x_252);
lean_ctor_set(x_255, 6, x_253);
lean_ctor_set(x_255, 7, x_254);
x_256 = lean_st_ref_set(x_14, x_255, x_246);
x_257 = lean_ctor_get(x_256, 1);
lean_inc(x_257);
lean_dec(x_256);
x_258 = lean_mk_string_unchecked("failed to create binder due to failure when reverting variable dependencies", 75, 75);
x_259 = l_Lean_stringToMessageData(x_258);
lean_dec(x_258);
x_260 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_259, x_11, x_12, x_13, x_14, x_257);
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_260, 1);
lean_inc(x_262);
lean_dec(x_260);
x_263 = lean_unbox(x_169);
x_264 = l_Lean_MVarId_setKind(x_29, x_263, x_11, x_12, x_13, x_14, x_262);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_265 = lean_ctor_get(x_264, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 x_266 = x_264;
} else {
 lean_dec_ref(x_264);
 x_266 = lean_box(0);
}
if (lean_is_scalar(x_266)) {
 x_267 = lean_alloc_ctor(1, 2, 0);
} else {
 x_267 = x_266;
 lean_ctor_set_tag(x_267, 1);
}
lean_ctor_set(x_267, 0, x_261);
lean_ctor_set(x_267, 1, x_265);
return x_267;
}
}
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_268 = lean_ctor_get(x_44, 0);
x_269 = lean_ctor_get(x_44, 1);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_44);
x_270 = lean_st_ref_get(x_14, x_269);
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_273 = x_270;
} else {
 lean_dec_ref(x_270);
 x_273 = lean_box(0);
}
x_274 = lean_box(2);
x_275 = lean_ctor_get(x_11, 2);
lean_inc(x_275);
x_276 = lean_ctor_get(x_39, 0);
lean_inc(x_276);
lean_dec(x_39);
x_277 = lean_ctor_get(x_42, 0);
lean_inc(x_277);
lean_dec(x_42);
x_278 = lean_ctor_get(x_268, 2);
lean_inc(x_278);
lean_dec(x_268);
x_279 = l_Lean_Environment_mainModule(x_276);
lean_dec(x_276);
if (lean_is_scalar(x_273)) {
 x_280 = lean_alloc_ctor(0, 2, 0);
} else {
 x_280 = x_273;
}
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_275);
x_281 = lean_ctor_get(x_271, 1);
lean_inc(x_281);
lean_dec(x_271);
x_282 = lean_unsigned_to_nat(8u);
x_283 = lean_unsigned_to_nat(2u);
x_284 = lean_nat_shiftl(x_282, x_283);
x_285 = lean_unsigned_to_nat(3u);
x_286 = lean_nat_div(x_284, x_285);
lean_dec(x_284);
x_287 = l_Nat_nextPowerOfTwo(x_286);
lean_dec(x_286);
x_288 = lean_box(0);
x_289 = lean_mk_array(x_287, x_288);
x_290 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_290, 0, x_17);
lean_ctor_set(x_290, 1, x_289);
x_291 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_291, 0, x_277);
lean_ctor_set(x_291, 1, x_281);
lean_ctor_set(x_291, 2, x_278);
lean_ctor_set(x_291, 3, x_290);
lean_inc(x_29);
x_292 = l_Lean_MetavarContext_revert(x_30, x_29, x_4, x_280, x_291);
lean_dec(x_291);
lean_dec(x_280);
lean_dec(x_30);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; uint8_t x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; size_t x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_292, 1);
lean_inc(x_294);
lean_dec(x_292);
x_295 = lean_st_ref_take(x_12, x_272);
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_295, 1);
lean_inc(x_297);
lean_dec(x_295);
x_298 = lean_ctor_get(x_294, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_296, 1);
lean_inc(x_299);
x_300 = lean_ctor_get(x_296, 2);
lean_inc(x_300);
x_301 = lean_ctor_get(x_296, 3);
lean_inc(x_301);
x_302 = lean_ctor_get(x_296, 4);
lean_inc(x_302);
lean_dec(x_296);
x_303 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_303, 0, x_298);
lean_ctor_set(x_303, 1, x_299);
lean_ctor_set(x_303, 2, x_300);
lean_ctor_set(x_303, 3, x_301);
lean_ctor_set(x_303, 4, x_302);
x_304 = lean_st_ref_set(x_12, x_303, x_297);
x_305 = lean_ctor_get(x_304, 1);
lean_inc(x_305);
lean_dec(x_304);
x_306 = lean_st_ref_take(x_14, x_305);
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_306, 1);
lean_inc(x_308);
lean_dec(x_306);
x_309 = lean_ctor_get(x_307, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_294, 1);
lean_inc(x_310);
x_311 = lean_ctor_get(x_294, 2);
lean_inc(x_311);
lean_dec(x_294);
x_312 = lean_ctor_get(x_307, 3);
lean_inc(x_312);
x_313 = lean_ctor_get(x_307, 4);
lean_inc(x_313);
x_314 = lean_ctor_get(x_307, 5);
lean_inc(x_314);
x_315 = lean_ctor_get(x_307, 6);
lean_inc(x_315);
x_316 = lean_ctor_get(x_307, 7);
lean_inc(x_316);
lean_dec(x_307);
x_317 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_317, 0, x_309);
lean_ctor_set(x_317, 1, x_310);
lean_ctor_set(x_317, 2, x_311);
lean_ctor_set(x_317, 3, x_312);
lean_ctor_set(x_317, 4, x_313);
lean_ctor_set(x_317, 5, x_314);
lean_ctor_set(x_317, 6, x_315);
lean_ctor_set(x_317, 7, x_316);
x_318 = lean_st_ref_set(x_14, x_317, x_308);
x_319 = lean_ctor_get(x_318, 1);
lean_inc(x_319);
lean_dec(x_318);
x_320 = lean_unbox(x_274);
x_321 = l_Lean_MVarId_setKind(x_29, x_320, x_11, x_12, x_13, x_14, x_319);
x_322 = lean_ctor_get(x_321, 1);
lean_inc(x_322);
lean_dec(x_321);
x_323 = lean_ctor_get(x_293, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_293, 1);
lean_inc(x_324);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 x_325 = x_293;
} else {
 lean_dec_ref(x_293);
 x_325 = lean_box(0);
}
x_326 = l_Lean_Expr_getAppFn(x_323);
lean_dec(x_323);
x_327 = l_Lean_Expr_mvarId_x21(x_326);
lean_dec(x_326);
x_328 = lean_unbox(x_274);
lean_inc(x_327);
x_329 = l_Lean_MVarId_setKind(x_327, x_328, x_11, x_12, x_13, x_14, x_322);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
x_330 = lean_ctor_get(x_329, 1);
lean_inc(x_330);
lean_dec(x_329);
lean_inc(x_327);
x_331 = l_Lean_MVarId_setTag___redArg(x_327, x_32, x_12, x_330);
lean_dec(x_12);
x_332 = lean_ctor_get(x_331, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 lean_ctor_release(x_331, 1);
 x_333 = x_331;
} else {
 lean_dec_ref(x_331);
 x_333 = lean_box(0);
}
x_334 = lean_array_size(x_324);
x_335 = l_Array_mapMUnsafe_map___at___Lean_MVarId_revert_spec__1(x_334, x_18, x_324);
if (lean_is_scalar(x_325)) {
 x_336 = lean_alloc_ctor(0, 2, 0);
} else {
 x_336 = x_325;
}
lean_ctor_set(x_336, 0, x_335);
lean_ctor_set(x_336, 1, x_327);
if (lean_is_scalar(x_333)) {
 x_337 = lean_alloc_ctor(0, 2, 0);
} else {
 x_337 = x_333;
}
lean_ctor_set(x_337, 0, x_336);
lean_ctor_set(x_337, 1, x_332);
return x_337;
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
lean_dec(x_32);
x_338 = lean_ctor_get(x_292, 1);
lean_inc(x_338);
lean_dec(x_292);
x_339 = lean_st_ref_take(x_12, x_272);
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_339, 1);
lean_inc(x_341);
lean_dec(x_339);
x_342 = lean_ctor_get(x_338, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_340, 1);
lean_inc(x_343);
x_344 = lean_ctor_get(x_340, 2);
lean_inc(x_344);
x_345 = lean_ctor_get(x_340, 3);
lean_inc(x_345);
x_346 = lean_ctor_get(x_340, 4);
lean_inc(x_346);
lean_dec(x_340);
x_347 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_347, 0, x_342);
lean_ctor_set(x_347, 1, x_343);
lean_ctor_set(x_347, 2, x_344);
lean_ctor_set(x_347, 3, x_345);
lean_ctor_set(x_347, 4, x_346);
x_348 = lean_st_ref_set(x_12, x_347, x_341);
x_349 = lean_ctor_get(x_348, 1);
lean_inc(x_349);
lean_dec(x_348);
x_350 = lean_st_ref_take(x_14, x_349);
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_350, 1);
lean_inc(x_352);
lean_dec(x_350);
x_353 = lean_ctor_get(x_351, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_338, 1);
lean_inc(x_354);
x_355 = lean_ctor_get(x_338, 2);
lean_inc(x_355);
lean_dec(x_338);
x_356 = lean_ctor_get(x_351, 3);
lean_inc(x_356);
x_357 = lean_ctor_get(x_351, 4);
lean_inc(x_357);
x_358 = lean_ctor_get(x_351, 5);
lean_inc(x_358);
x_359 = lean_ctor_get(x_351, 6);
lean_inc(x_359);
x_360 = lean_ctor_get(x_351, 7);
lean_inc(x_360);
lean_dec(x_351);
x_361 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_361, 0, x_353);
lean_ctor_set(x_361, 1, x_354);
lean_ctor_set(x_361, 2, x_355);
lean_ctor_set(x_361, 3, x_356);
lean_ctor_set(x_361, 4, x_357);
lean_ctor_set(x_361, 5, x_358);
lean_ctor_set(x_361, 6, x_359);
lean_ctor_set(x_361, 7, x_360);
x_362 = lean_st_ref_set(x_14, x_361, x_352);
x_363 = lean_ctor_get(x_362, 1);
lean_inc(x_363);
lean_dec(x_362);
x_364 = lean_mk_string_unchecked("failed to create binder due to failure when reverting variable dependencies", 75, 75);
x_365 = l_Lean_stringToMessageData(x_364);
lean_dec(x_364);
x_366 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_365, x_11, x_12, x_13, x_14, x_363);
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_366, 1);
lean_inc(x_368);
lean_dec(x_366);
x_369 = lean_unbox(x_274);
x_370 = l_Lean_MVarId_setKind(x_29, x_369, x_11, x_12, x_13, x_14, x_368);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_371 = lean_ctor_get(x_370, 1);
lean_inc(x_371);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 lean_ctor_release(x_370, 1);
 x_372 = x_370;
} else {
 lean_dec_ref(x_370);
 x_372 = lean_box(0);
}
if (lean_is_scalar(x_372)) {
 x_373 = lean_alloc_ctor(1, 2, 0);
} else {
 x_373 = x_372;
 lean_ctor_set_tag(x_373, 1);
}
lean_ctor_set(x_373, 0, x_367);
lean_ctor_set(x_373, 1, x_371);
return x_373;
}
}
}
else
{
uint8_t x_374; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_374 = !lean_is_exclusive(x_31);
if (x_374 == 0)
{
return x_31;
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_375 = lean_ctor_get(x_31, 0);
x_376 = lean_ctor_get(x_31, 1);
lean_inc(x_376);
lean_inc(x_375);
lean_dec(x_31);
x_377 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_377, 0, x_375);
lean_ctor_set(x_377, 1, x_376);
return x_377;
}
}
}
else
{
uint8_t x_378; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_378 = !lean_is_exclusive(x_26);
if (x_378 == 0)
{
return x_26;
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_379 = lean_ctor_get(x_26, 0);
x_380 = lean_ctor_get(x_26, 1);
lean_inc(x_380);
lean_inc(x_379);
lean_dec(x_26);
x_381 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_381, 0, x_379);
lean_ctor_set(x_381, 1, x_380);
return x_381;
}
}
}
else
{
uint8_t x_382; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_382 = !lean_is_exclusive(x_20);
if (x_382 == 0)
{
return x_20;
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_383 = lean_ctor_get(x_20, 0);
x_384 = lean_ctor_get(x_20, 1);
lean_inc(x_384);
lean_inc(x_383);
lean_dec(x_20);
x_385 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_385, 0, x_383);
lean_ctor_set(x_385, 1, x_384);
return x_385;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revert(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Array_isEmpty___redArg(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_mk_string_unchecked("revert", 6, 6);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_box(x_3);
x_14 = lean_box(x_4);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_Lean_MVarId_revert___lam__0___boxed), 10, 5);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_12);
lean_closure_set(x_15, 2, x_2);
lean_closure_set(x_15, 3, x_13);
lean_closure_set(x_15, 4, x_14);
x_16 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_15, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_mk_empty_array_with_capacity(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_9);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_MVarId_revert_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_MVarId_revert_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_MVarId_revert_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_MVarId_revert_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_MVarId_revert_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_MVarId_revert_spec__2_spec__2(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_MVarId_revert_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_MVarId_revert_spec__2(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_MVarId_revert___lam__0(x_1, x_2, x_3, x_11, x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_MVarId_revert(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0_spec__0_spec__0_spec__0(x_6, x_4);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0_spec__0_spec__0_spec__0_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_11; uint8_t x_14; 
x_14 = lean_usize_dec_eq(x_2, x_3);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_array_uget(x_1, x_2);
if (lean_obj_tag(x_15) == 0)
{
x_5 = x_4;
goto block_10;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_11 = x_17;
goto block_13;
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
block_13:
{
lean_object* x_12; 
x_12 = lean_array_push(x_4, x_11);
x_5 = x_12;
goto block_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_dec(x_5);
return x_2;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_5);
if (x_7 == 0)
{
lean_dec(x_5);
return x_2;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_usize_of_nat(x_4);
x_9 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_10 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0_spec__0_spec__0_spec__0_spec__0(x_3, x_8, x_9, x_2);
return x_10;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_11);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_dec(x_13);
return x_2;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_13, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
return x_2;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_usize_of_nat(x_12);
x_17 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_18 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0_spec__0_spec__0_spec__0_spec__1(x_11, x_16, x_17, x_2);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Lean_instInhabitedPersistentArrayNode(lean_box(0));
x_7 = lean_usize_shift_right(x_2, x_3);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_array_get(x_6, x_5, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_shift_left(x_11, x_3);
x_13 = lean_usize_sub(x_12, x_11);
x_14 = lean_usize_land(x_2, x_13);
x_15 = lean_unsigned_to_nat(5u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_sub(x_3, x_16);
x_18 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0_spec__0_spec__0(x_9, x_14, x_17, x_4);
lean_dec(x_9);
x_19 = lean_nat_add(x_8, x_10);
lean_dec(x_8);
x_20 = lean_array_get_size(x_5);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_dec(x_20);
lean_dec(x_19);
return x_18;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_le(x_20, x_20);
if (x_22 == 0)
{
lean_dec(x_20);
lean_dec(x_19);
return x_18;
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; 
x_23 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_24 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_25 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0_spec__0_spec__0_spec__0_spec__0(x_5, x_23, x_24, x_18);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_usize_to_nat(x_2);
x_28 = lean_array_get_size(x_26);
x_29 = lean_nat_dec_lt(x_27, x_28);
if (x_29 == 0)
{
lean_dec(x_28);
lean_dec(x_27);
return x_4;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_28, x_28);
if (x_30 == 0)
{
lean_dec(x_28);
lean_dec(x_27);
return x_4;
}
else
{
size_t x_31; size_t x_32; lean_object* x_33; 
x_31 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_32 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_33 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0_spec__0_spec__0_spec__0_spec__1(x_26, x_31, x_32, x_4);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_1, 3);
x_7 = lean_nat_dec_le(x_6, x_3);
if (x_7 == 0)
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_usize_of_nat(x_3);
x_10 = lean_ctor_get_usize(x_1, 4);
x_11 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0_spec__0_spec__0(x_8, x_9, x_10, x_2);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_array_get_size(x_12);
x_14 = lean_nat_dec_lt(x_4, x_13);
if (x_14 == 0)
{
lean_dec(x_13);
return x_11;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_13, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
return x_11;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_usize_of_nat(x_4);
x_17 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_18 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0_spec__0_spec__0_spec__0_spec__1(x_12, x_16, x_17, x_11);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_nat_sub(x_3, x_6);
x_21 = lean_array_get_size(x_19);
x_22 = lean_nat_dec_lt(x_20, x_21);
if (x_22 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
return x_2;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_21, x_21);
if (x_23 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
return x_2;
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; 
x_24 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_25 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_26 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0_spec__0_spec__0_spec__0_spec__1(x_19, x_24, x_25, x_2);
return x_26;
}
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_1, 0);
x_28 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0_spec__0_spec__0_spec__0(x_27, x_2);
x_29 = lean_ctor_get(x_1, 1);
x_30 = lean_array_get_size(x_29);
x_31 = lean_nat_dec_lt(x_4, x_30);
if (x_31 == 0)
{
lean_dec(x_30);
return x_28;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_30, x_30);
if (x_32 == 0)
{
lean_dec(x_30);
return x_28;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; 
x_33 = lean_usize_of_nat(x_4);
x_34 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_35 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0_spec__0_spec__0_spec__0_spec__1(x_29, x_33, x_34, x_28);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0_spec__0(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAfter___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_3);
x_8 = l_Lean_FVarId_getDecl___redArg(x_1, x_3, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_23; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_3, 2);
lean_inc(x_11);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_mk_empty_array_with_capacity(x_12);
x_23 = lean_ctor_get(x_9, 0);
lean_inc(x_23);
lean_dec(x_9);
x_14 = x_23;
goto block_22;
block_22:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_14, x_15);
lean_dec(x_14);
x_17 = l_Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0(x_11, x_13, x_16);
lean_dec(x_16);
lean_dec(x_11);
x_18 = lean_box(1);
x_19 = lean_unbox(x_18);
x_20 = lean_unbox(x_18);
x_21 = l_Lean_MVarId_revert(x_2, x_17, x_19, x_20, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_3);
return x_21;
}
}
else
{
uint8_t x_24; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_8);
if (x_24 == 0)
{
return x_8;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_8, 0);
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_8);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAfter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_MVarId_revertAfter___lam__0), 7, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0_spec__0_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0_spec__0_spec__0_spec__0_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0_spec__0_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0_spec__0_spec__0_spec__0_spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0_spec__0_spec__0_spec__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0_spec__0_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_LocalContext_foldlM___at___Lean_MVarId_revertAfter_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAfter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_revertAfter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
lean_object* initialize_Lean_Meta_Tactic_Clear(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Revert(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Clear(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
