// Lean compiler output
// Module: Lean.Util.FoldConsts
// Imports: Lean.Expr Lean.Util.PtrSet Lean.Declaration
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
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstantsAsSet(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_NameHashSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_getUsedConstantsAsSet(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstantsAsSet___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*, uint8_t);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_usize_to_uint64(size_t);
LEAN_EXPORT lean_object* l_Lean_RBTree_ofList___at___Lean_ConstantInfo_getUsedConstantsAsSet_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__1(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_append(lean_object*, lean_object*);
lean_object* l_Lean_mkPtrSet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstants___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameHashSet_insert(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstants(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__1___redArg(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; uint64_t x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; lean_object* x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; lean_object* x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; size_t x_20; size_t x_21; lean_object* x_22; size_t x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = lean_ptr_addr(x_4);
x_8 = lean_usize_to_uint64(x_7);
x_9 = lean_unsigned_to_nat(11u);
x_10 = lean_uint64_of_nat(x_9);
x_11 = lean_uint64_mix_hash(x_8, x_10);
x_12 = lean_unsigned_to_nat(32u);
x_13 = lean_uint64_of_nat(x_12);
x_14 = lean_uint64_shift_right(x_11, x_13);
x_15 = lean_uint64_xor(x_11, x_14);
x_16 = lean_unsigned_to_nat(16u);
x_17 = lean_uint64_of_nat(x_16);
x_18 = lean_uint64_shift_right(x_15, x_17);
x_19 = lean_uint64_xor(x_15, x_18);
x_20 = lean_uint64_to_usize(x_19);
x_21 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_usize_of_nat(x_22);
x_24 = lean_usize_sub(x_21, x_23);
x_25 = lean_usize_land(x_20, x_24);
x_26 = lean_array_uget(x_1, x_25);
lean_ctor_set(x_2, 2, x_26);
x_27 = lean_array_uset(x_1, x_25, x_2);
x_1 = x_27;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; uint64_t x_34; lean_object* x_35; uint64_t x_36; uint64_t x_37; lean_object* x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; lean_object* x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; size_t x_46; size_t x_47; lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_29 = lean_ctor_get(x_2, 0);
x_30 = lean_ctor_get(x_2, 1);
x_31 = lean_ctor_get(x_2, 2);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_2);
x_32 = lean_array_get_size(x_1);
x_33 = lean_ptr_addr(x_29);
x_34 = lean_usize_to_uint64(x_33);
x_35 = lean_unsigned_to_nat(11u);
x_36 = lean_uint64_of_nat(x_35);
x_37 = lean_uint64_mix_hash(x_34, x_36);
x_38 = lean_unsigned_to_nat(32u);
x_39 = lean_uint64_of_nat(x_38);
x_40 = lean_uint64_shift_right(x_37, x_39);
x_41 = lean_uint64_xor(x_37, x_40);
x_42 = lean_unsigned_to_nat(16u);
x_43 = lean_uint64_of_nat(x_42);
x_44 = lean_uint64_shift_right(x_41, x_43);
x_45 = lean_uint64_xor(x_41, x_44);
x_46 = lean_uint64_to_usize(x_45);
x_47 = lean_usize_of_nat(x_32);
lean_dec(x_32);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_usize_of_nat(x_48);
x_50 = lean_usize_sub(x_47, x_49);
x_51 = lean_usize_land(x_46, x_50);
x_52 = lean_array_uget(x_1, x_51);
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_29);
lean_ctor_set(x_53, 1, x_30);
lean_ctor_set(x_53, 2, x_52);
x_54 = lean_array_uset(x_1, x_51, x_53);
x_1 = x_54;
x_2 = x_31;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__1_spec__1___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__1___redArg(lean_object* x_1) {
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
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__1___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_8 = l_Lean_Expr_FoldConstsImpl_fold_visit___redArg(x_1, x_4, x_2, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Expr_FoldConstsImpl_fold_visit___redArg(x_1, x_5, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; uint64_t x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; lean_object* x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; size_t x_21; size_t x_22; lean_object* x_23; size_t x_24; size_t x_25; size_t x_26; lean_object* x_27; uint8_t x_28; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
x_8 = lean_ptr_addr(x_2);
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
x_27 = lean_array_uget(x_6, x_26);
lean_dec(x_6);
x_28 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__0___redArg(x_2, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_73; size_t x_74; size_t x_75; size_t x_76; lean_object* x_77; uint8_t x_78; 
x_29 = lean_ctor_get(x_5, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_5, 1);
lean_inc(x_30);
x_73 = lean_array_get_size(x_30);
x_74 = lean_usize_of_nat(x_73);
lean_dec(x_73);
x_75 = lean_usize_sub(x_74, x_24);
x_76 = lean_usize_land(x_21, x_75);
x_77 = lean_array_uget(x_30, x_76);
x_78 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__0___redArg(x_2, x_77);
if (x_78 == 0)
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_5);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_80 = lean_ctor_get(x_5, 1);
lean_dec(x_80);
x_81 = lean_ctor_get(x_5, 0);
lean_dec(x_81);
x_82 = lean_box(0);
x_83 = lean_nat_add(x_29, x_23);
lean_dec(x_29);
lean_inc(x_2);
x_84 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_84, 0, x_2);
lean_ctor_set(x_84, 1, x_82);
lean_ctor_set(x_84, 2, x_77);
x_85 = lean_array_uset(x_30, x_76, x_84);
x_86 = lean_unsigned_to_nat(2u);
x_87 = lean_nat_shiftl(x_83, x_86);
x_88 = lean_unsigned_to_nat(3u);
x_89 = lean_nat_div(x_87, x_88);
lean_dec(x_87);
x_90 = lean_array_get_size(x_85);
x_91 = lean_nat_dec_le(x_89, x_90);
lean_dec(x_90);
lean_dec(x_89);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__1___redArg(x_85);
lean_ctor_set(x_5, 1, x_92);
lean_ctor_set(x_5, 0, x_83);
x_31 = x_5;
goto block_72;
}
else
{
lean_ctor_set(x_5, 1, x_85);
lean_ctor_set(x_5, 0, x_83);
x_31 = x_5;
goto block_72;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
lean_dec(x_5);
x_93 = lean_box(0);
x_94 = lean_nat_add(x_29, x_23);
lean_dec(x_29);
lean_inc(x_2);
x_95 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_95, 0, x_2);
lean_ctor_set(x_95, 1, x_93);
lean_ctor_set(x_95, 2, x_77);
x_96 = lean_array_uset(x_30, x_76, x_95);
x_97 = lean_unsigned_to_nat(2u);
x_98 = lean_nat_shiftl(x_94, x_97);
x_99 = lean_unsigned_to_nat(3u);
x_100 = lean_nat_div(x_98, x_99);
lean_dec(x_98);
x_101 = lean_array_get_size(x_96);
x_102 = lean_nat_dec_le(x_100, x_101);
lean_dec(x_101);
lean_dec(x_100);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__1___redArg(x_96);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_94);
lean_ctor_set(x_104, 1, x_103);
x_31 = x_104;
goto block_72;
}
else
{
lean_object* x_105; 
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_94);
lean_ctor_set(x_105, 1, x_96);
x_31 = x_105;
goto block_72;
}
}
}
else
{
lean_dec(x_77);
lean_dec(x_30);
lean_dec(x_29);
x_31 = x_5;
goto block_72;
}
block_72:
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_4, 1);
lean_inc(x_32);
lean_dec(x_4);
lean_inc(x_32);
lean_inc(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
switch (lean_obj_tag(x_2)) {
case 4:
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
lean_dec(x_2);
x_35 = l_Lean_NameHashSet_contains(x_32, x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_33);
lean_inc(x_34);
x_36 = l_Lean_NameHashSet_insert(x_32, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_apply_2(x_1, x_34, x_3);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
else
{
lean_object* x_40; 
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_1);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_3);
lean_ctor_set(x_40, 1, x_33);
return x_40;
}
}
case 5:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_32);
lean_dec(x_31);
x_41 = lean_ctor_get(x_2, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_2, 1);
lean_inc(x_42);
lean_dec(x_2);
lean_inc(x_1);
x_43 = l_Lean_Expr_FoldConstsImpl_fold_visit___redArg(x_1, x_41, x_3, x_33);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_2 = x_42;
x_3 = x_44;
x_4 = x_45;
goto _start;
}
case 6:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; 
lean_dec(x_32);
lean_dec(x_31);
x_47 = lean_ctor_get(x_2, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_2, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_2, 2);
lean_inc(x_49);
x_50 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
x_51 = l_Lean_Expr_FoldConstsImpl_fold_visit___redArg___lam__0(x_1, x_3, x_47, x_48, x_49, x_50, x_33);
lean_dec(x_47);
return x_51;
}
case 7:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; 
lean_dec(x_32);
lean_dec(x_31);
x_52 = lean_ctor_get(x_2, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_2, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_2, 2);
lean_inc(x_54);
x_55 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
x_56 = l_Lean_Expr_FoldConstsImpl_fold_visit___redArg___lam__0(x_1, x_3, x_52, x_53, x_54, x_55, x_33);
lean_dec(x_52);
return x_56;
}
case 8:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_32);
lean_dec(x_31);
x_57 = lean_ctor_get(x_2, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_2, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_2, 3);
lean_inc(x_59);
lean_dec(x_2);
lean_inc(x_1);
x_60 = l_Lean_Expr_FoldConstsImpl_fold_visit___redArg(x_1, x_57, x_3, x_33);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
lean_inc(x_1);
x_63 = l_Lean_Expr_FoldConstsImpl_fold_visit___redArg(x_1, x_58, x_61, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_2 = x_59;
x_3 = x_64;
x_4 = x_65;
goto _start;
}
case 10:
{
lean_object* x_67; 
lean_dec(x_32);
lean_dec(x_31);
x_67 = lean_ctor_get(x_2, 1);
lean_inc(x_67);
lean_dec(x_2);
x_2 = x_67;
x_4 = x_33;
goto _start;
}
case 11:
{
lean_object* x_69; 
lean_dec(x_32);
lean_dec(x_31);
x_69 = lean_ctor_get(x_2, 2);
lean_inc(x_69);
lean_dec(x_2);
x_2 = x_69;
x_4 = x_33;
goto _start;
}
default: 
{
lean_object* x_71; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_2);
lean_dec(x_1);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_3);
lean_ctor_set(x_71, 1, x_33);
return x_71;
}
}
}
}
else
{
lean_object* x_106; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_3);
lean_ctor_set(x_106, 1, x_4);
return x_106;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Expr_FoldConstsImpl_fold_visit___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_FoldConstsImpl_fold_visit_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_6);
lean_dec(x_6);
x_9 = l_Lean_Expr_FoldConstsImpl_fold_visit___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_8, x_7);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_FoldConstsImpl_fold_visit___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Expr_FoldConstsImpl_fold_visit___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_4 = lean_unsigned_to_nat(64u);
x_5 = l_Lean_mkPtrSet(lean_box(0), x_4);
x_6 = lean_unsigned_to_nat(8u);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_shiftl(x_6, x_8);
x_10 = lean_unsigned_to_nat(3u);
x_11 = lean_nat_div(x_9, x_10);
lean_dec(x_9);
x_12 = l_Nat_nextPowerOfTwo(x_11);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = lean_mk_array(x_12, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Expr_FoldConstsImpl_fold_visit___redArg(x_3, x_1, x_2, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_5 = lean_unsigned_to_nat(64u);
x_6 = l_Lean_mkPtrSet(lean_box(0), x_5);
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
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Expr_FoldConstsImpl_fold_visit___redArg(x_4, x_2, x_3, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstants___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstants(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_getUsedConstants___lam__0), 2, 0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_unsigned_to_nat(64u);
x_6 = l_Lean_mkPtrSet(lean_box(0), x_5);
x_7 = lean_unsigned_to_nat(8u);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_shiftl(x_7, x_8);
x_10 = lean_unsigned_to_nat(3u);
x_11 = lean_nat_div(x_9, x_10);
lean_dec(x_9);
x_12 = l_Nat_nextPowerOfTwo(x_11);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = lean_mk_array(x_12, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Expr_FoldConstsImpl_fold_visit___redArg(x_2, x_1, x_4, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstantsAsSet___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_NameSet_insert(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstantsAsSet(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_getUsedConstantsAsSet___lam__0), 2, 0);
x_3 = lean_box(0);
x_4 = lean_unsigned_to_nat(64u);
x_5 = l_Lean_mkPtrSet(lean_box(0), x_4);
x_6 = lean_unsigned_to_nat(8u);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_shiftl(x_6, x_8);
x_10 = lean_unsigned_to_nat(3u);
x_11 = lean_nat_div(x_9, x_10);
lean_dec(x_9);
x_12 = l_Nat_nextPowerOfTwo(x_11);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = lean_mk_array(x_12, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Expr_FoldConstsImpl_fold_visit___redArg(x_2, x_1, x_3, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_ofList___at___Lean_ConstantInfo_getUsedConstantsAsSet_spec__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_RBTree_ofList___at___Lean_ConstantInfo_getUsedConstantsAsSet_spec__0(x_4);
x_6 = lean_box(0);
x_7 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_5, x_3, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_getUsedConstantsAsSet(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_ConstantInfo_type(x_1);
x_3 = l_Lean_Expr_getUsedConstantsAsSet(x_2);
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
lean_inc(x_1);
x_6 = l_Lean_ConstantInfo_value_x3f(x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Expr_getUsedConstantsAsSet(x_8);
x_10 = l_Lean_NameSet_append(x_3, x_9);
return x_10;
}
case 5:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 4);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_RBTree_ofList___at___Lean_ConstantInfo_getUsedConstantsAsSet_spec__0(x_12);
x_14 = l_Lean_NameSet_append(x_3, x_13);
return x_14;
}
case 6:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_NameSet_insert(x_16, x_18);
x_20 = l_Lean_NameSet_append(x_3, x_19);
return x_20;
}
case 7:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_RBTree_ofList___at___Lean_ConstantInfo_getUsedConstantsAsSet_spec__0(x_22);
x_24 = l_Lean_NameSet_append(x_3, x_23);
return x_24;
}
default: 
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_1);
x_25 = lean_box(0);
x_26 = l_Lean_NameSet_append(x_3, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_27 = lean_ctor_get(x_6, 0);
lean_inc(x_27);
lean_dec(x_6);
x_28 = l_Lean_Expr_getUsedConstantsAsSet(x_27);
x_29 = l_Lean_NameSet_append(x_3, x_28);
return x_29;
}
}
}
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_PtrSet(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Declaration(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_FoldConsts(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_PtrSet(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Declaration(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
