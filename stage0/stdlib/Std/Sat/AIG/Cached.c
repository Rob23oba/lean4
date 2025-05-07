// Lean compiler output
// Module: Std.Sat.AIG.Cached
// Imports: Std.Sat.AIG.Basic Std.Sat.AIG.Lemmas
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*);
lean_object* l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_533____boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_793_(lean_object*, lean_object*, lean_object*);
lean_object* l_Bool_toNat(uint8_t);
uint8_t l_Std_DHashMap_Internal_AssocList_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_getConstant___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint64_t l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_533_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___redArg(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___redArg___boxed(lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_mkAtomCached___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_mkAtomCached___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_decEqDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_793_(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint64_t x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; lean_object* x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; size_t x_23; size_t x_24; lean_object* x_25; size_t x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_7 = x_3;
} else {
 lean_dec_ref(x_3);
 x_7 = lean_box(0);
}
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkAtomCached___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_10, 0, x_2);
x_11 = l_instBEqOfDecidableEq___redArg(x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_4);
x_13 = lean_array_get_size(x_9);
lean_inc(x_12);
lean_inc(x_1);
x_14 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_533_(x_1, x_12);
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
x_29 = lean_array_uget(x_9, x_28);
lean_inc(x_29);
lean_inc(x_12);
lean_inc(x_11);
x_30 = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(x_11, x_12, x_29);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_5);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_43; 
x_32 = lean_ctor_get(x_5, 1);
lean_dec(x_32);
x_33 = lean_ctor_get(x_5, 0);
lean_dec(x_33);
x_34 = lean_array_get_size(x_6);
lean_inc(x_29);
lean_inc(x_12);
lean_inc(x_11);
x_43 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_11, x_12, x_29);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_11);
x_44 = lean_nat_add(x_8, x_25);
lean_dec(x_8);
lean_inc(x_34);
lean_inc(x_12);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_12);
lean_ctor_set(x_45, 1, x_34);
lean_ctor_set(x_45, 2, x_29);
x_46 = lean_array_uset(x_9, x_28, x_45);
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
lean_object* x_53; lean_object* x_54; 
x_53 = lean_alloc_closure((void*)(l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_533____boxed), 3, 2);
lean_closure_set(x_53, 0, lean_box(0));
lean_closure_set(x_53, 1, x_1);
x_54 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_53, x_46);
lean_ctor_set(x_5, 1, x_54);
lean_ctor_set(x_5, 0, x_44);
x_35 = x_5;
goto block_42;
}
else
{
lean_dec(x_1);
lean_ctor_set(x_5, 1, x_46);
lean_ctor_set(x_5, 0, x_44);
x_35 = x_5;
goto block_42;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_1);
x_55 = lean_box(0);
x_56 = lean_array_uset(x_9, x_28, x_55);
lean_inc(x_34);
lean_inc(x_12);
x_57 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_11, x_12, x_34, x_29);
x_58 = lean_array_uset(x_56, x_28, x_57);
lean_ctor_set(x_5, 1, x_58);
x_35 = x_5;
goto block_42;
}
block_42:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_36 = lean_array_push(x_6, x_12);
if (lean_is_scalar(x_7)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_7;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_39, 0, x_34);
x_40 = lean_unbox(x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_40);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_68; 
lean_dec(x_5);
x_59 = lean_array_get_size(x_6);
lean_inc(x_29);
lean_inc(x_12);
lean_inc(x_11);
x_68 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_11, x_12, x_29);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec(x_11);
x_69 = lean_nat_add(x_8, x_25);
lean_dec(x_8);
lean_inc(x_59);
lean_inc(x_12);
x_70 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_70, 0, x_12);
lean_ctor_set(x_70, 1, x_59);
lean_ctor_set(x_70, 2, x_29);
x_71 = lean_array_uset(x_9, x_28, x_70);
x_72 = lean_unsigned_to_nat(2u);
x_73 = lean_nat_shiftl(x_69, x_72);
x_74 = lean_unsigned_to_nat(3u);
x_75 = lean_nat_div(x_73, x_74);
lean_dec(x_73);
x_76 = lean_array_get_size(x_71);
x_77 = lean_nat_dec_le(x_75, x_76);
lean_dec(x_76);
lean_dec(x_75);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_alloc_closure((void*)(l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_533____boxed), 3, 2);
lean_closure_set(x_78, 0, lean_box(0));
lean_closure_set(x_78, 1, x_1);
x_79 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_78, x_71);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_69);
lean_ctor_set(x_80, 1, x_79);
x_60 = x_80;
goto block_67;
}
else
{
lean_object* x_81; 
lean_dec(x_1);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_69);
lean_ctor_set(x_81, 1, x_71);
x_60 = x_81;
goto block_67;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_1);
x_82 = lean_box(0);
x_83 = lean_array_uset(x_9, x_28, x_82);
lean_inc(x_59);
lean_inc(x_12);
x_84 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_11, x_12, x_59, x_29);
x_85 = lean_array_uset(x_83, x_28, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_8);
lean_ctor_set(x_86, 1, x_85);
x_60 = x_86;
goto block_67;
}
block_67:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; 
x_61 = lean_array_push(x_6, x_12);
if (lean_is_scalar(x_7)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_7;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_64, 0, x_59);
x_65 = lean_unbox(x_63);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_65);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_62);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; 
lean_dec(x_29);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_87 = lean_ctor_get(x_30, 0);
lean_inc(x_87);
lean_dec(x_30);
if (lean_is_scalar(x_7)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_7;
}
lean_ctor_set(x_88, 0, x_6);
lean_ctor_set(x_88, 1, x_5);
x_89 = lean_box(0);
x_90 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_90, 0, x_87);
x_91 = lean_unbox(x_89);
lean_ctor_set_uint8(x_90, sizeof(void*)*1, x_91);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_88);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Sat_AIG_mkAtomCached___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAtomCached___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_Sat_AIG_mkAtomCached___redArg___lam__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___redArg(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*1, x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Std_Sat_AIG_mkConstCached___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkConstCached___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Std_Sat_AIG_mkConstCached(x_1, x_2, x_3, x_4, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint64_t x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; lean_object* x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkAtomCached___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_10, 0, x_2);
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_11, 0);
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_ctor_get(x_13, 0);
x_15 = lean_ctor_get_uint8(x_11, sizeof(void*)*1);
x_16 = lean_ctor_get_uint8(x_13, sizeof(void*)*1);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_shiftl(x_12, x_17);
x_19 = l_Bool_toNat(x_15);
x_20 = lean_nat_shiftl(x_14, x_17);
x_21 = l_Bool_toNat(x_16);
x_22 = lean_nat_lor(x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
x_23 = lean_nat_lor(x_20, x_21);
lean_dec(x_21);
lean_dec(x_20);
x_24 = l_instBEqOfDecidableEq___redArg(x_10);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_array_get_size(x_9);
lean_inc(x_25);
lean_inc(x_1);
x_27 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_533_(x_1, x_25);
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
x_38 = lean_usize_of_nat(x_17);
x_39 = lean_usize_sub(x_37, x_38);
x_40 = lean_usize_land(x_36, x_39);
x_41 = lean_array_uget(x_9, x_40);
lean_inc(x_41);
lean_inc(x_25);
lean_inc(x_24);
x_42 = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(x_24, x_25, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; uint8_t x_47; uint8_t x_52; lean_object* x_62; lean_object* x_63; 
lean_inc(x_6);
lean_inc(x_7);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_43 = x_6;
} else {
 lean_dec_ref(x_6);
 x_43 = lean_box(0);
}
x_62 = l_Std_Sat_AIG_getConstant___redArg(x_3, x_11);
x_63 = l_Std_Sat_AIG_getConstant___redArg(x_3, x_13);
if (lean_obj_tag(x_62) == 0)
{
lean_dec(x_43);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
x_64 = lean_nat_dec_eq(x_12, x_14);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; uint8_t x_72; 
lean_dec(x_3);
x_65 = lean_array_get_size(x_7);
lean_inc(x_41);
lean_inc(x_25);
lean_inc(x_24);
x_72 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_24, x_25, x_41);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
lean_dec(x_24);
x_73 = lean_nat_add(x_8, x_17);
lean_dec(x_8);
lean_inc(x_65);
lean_inc(x_25);
x_74 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_74, 0, x_25);
lean_ctor_set(x_74, 1, x_65);
lean_ctor_set(x_74, 2, x_41);
x_75 = lean_array_uset(x_9, x_40, x_74);
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
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_alloc_closure((void*)(l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_533____boxed), 3, 2);
lean_closure_set(x_82, 0, lean_box(0));
lean_closure_set(x_82, 1, x_1);
x_83 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_82, x_75);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_73);
lean_ctor_set(x_84, 1, x_83);
x_66 = x_84;
goto block_71;
}
else
{
lean_object* x_85; 
lean_dec(x_1);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_73);
lean_ctor_set(x_85, 1, x_75);
x_66 = x_85;
goto block_71;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_1);
x_86 = lean_box(0);
x_87 = lean_array_uset(x_9, x_40, x_86);
lean_inc(x_65);
lean_inc(x_25);
x_88 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_24, x_25, x_65, x_41);
x_89 = lean_array_uset(x_87, x_40, x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_8);
lean_ctor_set(x_90, 1, x_89);
x_66 = x_90;
goto block_71;
}
block_71:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_array_push(x_7, x_25);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
x_69 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_69, 0, x_65);
lean_ctor_set_uint8(x_69, sizeof(void*)*1, x_64);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
else
{
lean_object* x_91; 
lean_dec(x_41);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_91 = lean_box(0);
if (x_15 == 0)
{
if (x_16 == 0)
{
x_52 = x_64;
goto block_55;
}
else
{
uint8_t x_92; 
x_92 = lean_unbox(x_91);
x_47 = x_92;
goto block_51;
}
}
else
{
if (x_16 == 0)
{
uint8_t x_93; 
x_93 = lean_unbox(x_91);
x_47 = x_93;
goto block_51;
}
else
{
x_52 = x_64;
goto block_55;
}
}
}
}
else
{
lean_object* x_94; uint8_t x_95; 
lean_dec(x_41);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_94 = lean_ctor_get(x_63, 0);
lean_inc(x_94);
lean_dec(x_63);
x_95 = lean_unbox(x_94);
lean_dec(x_94);
if (x_95 == 0)
{
goto block_61;
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_inc(x_12);
x_96 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_96, 0, x_12);
lean_ctor_set_uint8(x_96, sizeof(void*)*1, x_15);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_3);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
lean_object* x_98; uint8_t x_99; 
lean_dec(x_41);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_98 = lean_ctor_get(x_62, 0);
lean_inc(x_98);
lean_dec(x_62);
x_99 = lean_unbox(x_98);
lean_dec(x_98);
if (x_99 == 0)
{
lean_dec(x_63);
lean_dec(x_43);
goto block_61;
}
else
{
if (lean_obj_tag(x_63) == 0)
{
goto block_46;
}
else
{
lean_object* x_100; uint8_t x_101; 
x_100 = lean_ctor_get(x_63, 0);
lean_inc(x_100);
lean_dec(x_63);
x_101 = lean_unbox(x_100);
lean_dec(x_100);
if (x_101 == 0)
{
lean_dec(x_43);
goto block_61;
}
else
{
goto block_46;
}
}
}
}
block_46:
{
lean_object* x_44; lean_object* x_45; 
lean_inc(x_14);
x_44 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_44, 0, x_14);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_16);
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_3);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
block_51:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_47);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_3);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
block_55:
{
if (x_52 == 0)
{
x_47 = x_52;
goto block_51;
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_inc(x_12);
x_53 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_53, 0, x_12);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_15);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_3);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
block_61:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; 
x_56 = lean_box(0);
x_57 = lean_unsigned_to_nat(0u);
x_58 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_unbox(x_56);
lean_ctor_set_uint8(x_58, sizeof(void*)*1, x_59);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_3);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
lean_object* x_102; uint8_t x_103; 
lean_dec(x_41);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_102 = lean_ctor_get(x_42, 0);
lean_inc(x_102);
lean_dec(x_42);
lean_inc(x_6);
x_103 = !lean_is_exclusive(x_6);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_104 = lean_ctor_get(x_6, 1);
lean_dec(x_104);
x_105 = lean_ctor_get(x_6, 0);
lean_dec(x_105);
x_106 = lean_box(0);
x_107 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_107, 0, x_102);
x_108 = lean_unbox(x_106);
lean_ctor_set_uint8(x_107, sizeof(void*)*1, x_108);
lean_ctor_set(x_6, 1, x_107);
lean_ctor_set(x_6, 0, x_3);
return x_6;
}
else
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; 
lean_dec(x_6);
x_109 = lean_box(0);
x_110 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_110, 0, x_102);
x_111 = lean_unbox(x_109);
lean_ctor_set_uint8(x_110, sizeof(void*)*1, x_111);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_3);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint64_t x_134; lean_object* x_135; uint64_t x_136; uint64_t x_137; uint64_t x_138; lean_object* x_139; uint64_t x_140; uint64_t x_141; uint64_t x_142; size_t x_143; size_t x_144; size_t x_145; size_t x_146; size_t x_147; lean_object* x_148; lean_object* x_149; 
x_113 = lean_ctor_get(x_3, 1);
x_114 = lean_ctor_get(x_3, 0);
lean_inc(x_113);
lean_inc(x_114);
lean_dec(x_3);
x_115 = lean_ctor_get(x_113, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
x_117 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkAtomCached___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_117, 0, x_2);
x_118 = lean_ctor_get(x_4, 0);
x_119 = lean_ctor_get(x_118, 0);
x_120 = lean_ctor_get(x_4, 1);
x_121 = lean_ctor_get(x_120, 0);
x_122 = lean_ctor_get_uint8(x_118, sizeof(void*)*1);
x_123 = lean_ctor_get_uint8(x_120, sizeof(void*)*1);
x_124 = lean_unsigned_to_nat(1u);
x_125 = lean_nat_shiftl(x_119, x_124);
x_126 = l_Bool_toNat(x_122);
x_127 = lean_nat_shiftl(x_121, x_124);
x_128 = l_Bool_toNat(x_123);
x_129 = lean_nat_lor(x_125, x_126);
lean_dec(x_126);
lean_dec(x_125);
x_130 = lean_nat_lor(x_127, x_128);
lean_dec(x_128);
lean_dec(x_127);
x_131 = l_instBEqOfDecidableEq___redArg(x_117);
x_132 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_130);
x_133 = lean_array_get_size(x_116);
lean_inc(x_132);
lean_inc(x_1);
x_134 = l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl___redArg____x40_Std_Sat_AIG_Basic___hyg_533_(x_1, x_132);
x_135 = lean_unsigned_to_nat(32u);
x_136 = lean_uint64_of_nat(x_135);
x_137 = lean_uint64_shift_right(x_134, x_136);
x_138 = lean_uint64_xor(x_134, x_137);
x_139 = lean_unsigned_to_nat(16u);
x_140 = lean_uint64_of_nat(x_139);
x_141 = lean_uint64_shift_right(x_138, x_140);
x_142 = lean_uint64_xor(x_138, x_141);
x_143 = lean_uint64_to_usize(x_142);
x_144 = lean_usize_of_nat(x_133);
lean_dec(x_133);
x_145 = lean_usize_of_nat(x_124);
x_146 = lean_usize_sub(x_144, x_145);
x_147 = lean_usize_land(x_143, x_146);
x_148 = lean_array_uget(x_116, x_147);
lean_inc(x_148);
lean_inc(x_132);
lean_inc(x_131);
x_149 = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(x_131, x_132, x_148);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; uint8_t x_155; uint8_t x_160; lean_object* x_170; lean_object* x_171; 
lean_inc(x_113);
lean_inc(x_114);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_114);
lean_ctor_set(x_150, 1, x_113);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_151 = x_113;
} else {
 lean_dec_ref(x_113);
 x_151 = lean_box(0);
}
x_170 = l_Std_Sat_AIG_getConstant___redArg(x_150, x_118);
x_171 = l_Std_Sat_AIG_getConstant___redArg(x_150, x_120);
if (lean_obj_tag(x_170) == 0)
{
lean_dec(x_151);
if (lean_obj_tag(x_171) == 0)
{
uint8_t x_172; 
x_172 = lean_nat_dec_eq(x_119, x_121);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; uint8_t x_180; 
lean_dec(x_150);
x_173 = lean_array_get_size(x_114);
lean_inc(x_148);
lean_inc(x_132);
lean_inc(x_131);
x_180 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_131, x_132, x_148);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
lean_dec(x_131);
x_181 = lean_nat_add(x_115, x_124);
lean_dec(x_115);
lean_inc(x_173);
lean_inc(x_132);
x_182 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_182, 0, x_132);
lean_ctor_set(x_182, 1, x_173);
lean_ctor_set(x_182, 2, x_148);
x_183 = lean_array_uset(x_116, x_147, x_182);
x_184 = lean_unsigned_to_nat(2u);
x_185 = lean_nat_shiftl(x_181, x_184);
x_186 = lean_unsigned_to_nat(3u);
x_187 = lean_nat_div(x_185, x_186);
lean_dec(x_185);
x_188 = lean_array_get_size(x_183);
x_189 = lean_nat_dec_le(x_187, x_188);
lean_dec(x_188);
lean_dec(x_187);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_alloc_closure((void*)(l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_hashDecl____x40_Std_Sat_AIG_Basic___hyg_533____boxed), 3, 2);
lean_closure_set(x_190, 0, lean_box(0));
lean_closure_set(x_190, 1, x_1);
x_191 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_190, x_183);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_181);
lean_ctor_set(x_192, 1, x_191);
x_174 = x_192;
goto block_179;
}
else
{
lean_object* x_193; 
lean_dec(x_1);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_181);
lean_ctor_set(x_193, 1, x_183);
x_174 = x_193;
goto block_179;
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_1);
x_194 = lean_box(0);
x_195 = lean_array_uset(x_116, x_147, x_194);
lean_inc(x_173);
lean_inc(x_132);
x_196 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_131, x_132, x_173, x_148);
x_197 = lean_array_uset(x_195, x_147, x_196);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_115);
lean_ctor_set(x_198, 1, x_197);
x_174 = x_198;
goto block_179;
}
block_179:
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_175 = lean_array_push(x_114, x_132);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_174);
x_177 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_177, 0, x_173);
lean_ctor_set_uint8(x_177, sizeof(void*)*1, x_172);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
else
{
lean_object* x_199; 
lean_dec(x_148);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_1);
x_199 = lean_box(0);
if (x_122 == 0)
{
if (x_123 == 0)
{
x_160 = x_172;
goto block_163;
}
else
{
uint8_t x_200; 
x_200 = lean_unbox(x_199);
x_155 = x_200;
goto block_159;
}
}
else
{
if (x_123 == 0)
{
uint8_t x_201; 
x_201 = lean_unbox(x_199);
x_155 = x_201;
goto block_159;
}
else
{
x_160 = x_172;
goto block_163;
}
}
}
}
else
{
lean_object* x_202; uint8_t x_203; 
lean_dec(x_148);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_1);
x_202 = lean_ctor_get(x_171, 0);
lean_inc(x_202);
lean_dec(x_171);
x_203 = lean_unbox(x_202);
lean_dec(x_202);
if (x_203 == 0)
{
goto block_169;
}
else
{
lean_object* x_204; lean_object* x_205; 
lean_inc(x_119);
x_204 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_204, 0, x_119);
lean_ctor_set_uint8(x_204, sizeof(void*)*1, x_122);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_150);
lean_ctor_set(x_205, 1, x_204);
return x_205;
}
}
}
else
{
lean_object* x_206; uint8_t x_207; 
lean_dec(x_148);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_1);
x_206 = lean_ctor_get(x_170, 0);
lean_inc(x_206);
lean_dec(x_170);
x_207 = lean_unbox(x_206);
lean_dec(x_206);
if (x_207 == 0)
{
lean_dec(x_171);
lean_dec(x_151);
goto block_169;
}
else
{
if (lean_obj_tag(x_171) == 0)
{
goto block_154;
}
else
{
lean_object* x_208; uint8_t x_209; 
x_208 = lean_ctor_get(x_171, 0);
lean_inc(x_208);
lean_dec(x_171);
x_209 = lean_unbox(x_208);
lean_dec(x_208);
if (x_209 == 0)
{
lean_dec(x_151);
goto block_169;
}
else
{
goto block_154;
}
}
}
}
block_154:
{
lean_object* x_152; lean_object* x_153; 
lean_inc(x_121);
x_152 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_152, 0, x_121);
lean_ctor_set_uint8(x_152, sizeof(void*)*1, x_123);
if (lean_is_scalar(x_151)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_151;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
block_159:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_unsigned_to_nat(0u);
x_157 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set_uint8(x_157, sizeof(void*)*1, x_155);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_150);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
block_163:
{
if (x_160 == 0)
{
x_155 = x_160;
goto block_159;
}
else
{
lean_object* x_161; lean_object* x_162; 
lean_inc(x_119);
x_161 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_161, 0, x_119);
lean_ctor_set_uint8(x_161, sizeof(void*)*1, x_122);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_150);
lean_ctor_set(x_162, 1, x_161);
return x_162;
}
}
block_169:
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; 
x_164 = lean_box(0);
x_165 = lean_unsigned_to_nat(0u);
x_166 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_166, 0, x_165);
x_167 = lean_unbox(x_164);
lean_ctor_set_uint8(x_166, sizeof(void*)*1, x_167);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_150);
lean_ctor_set(x_168, 1, x_166);
return x_168;
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; lean_object* x_216; 
lean_dec(x_148);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_1);
x_210 = lean_ctor_get(x_149, 0);
lean_inc(x_210);
lean_dec(x_149);
lean_inc(x_113);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_114);
lean_ctor_set(x_211, 1, x_113);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_212 = x_113;
} else {
 lean_dec_ref(x_113);
 x_212 = lean_box(0);
}
x_213 = lean_box(0);
x_214 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_214, 0, x_210);
x_215 = lean_unbox(x_213);
lean_ctor_set_uint8(x_214, sizeof(void*)*1, x_215);
if (lean_is_scalar(x_212)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_212;
}
lean_ctor_set(x_216, 0, x_211);
lean_ctor_set(x_216, 1, x_214);
return x_216;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Sat_AIG_mkGateCached_go___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Sat_AIG_mkGateCached_go___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Sat_AIG_mkGateCached_go(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_nat_dec_lt(x_6, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_5);
lean_inc(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_5);
x_11 = l_Std_Sat_AIG_mkGateCached_go___redArg(x_1, x_2, x_3, x_10);
lean_dec(x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_7);
lean_inc(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_7);
x_13 = l_Std_Sat_AIG_mkGateCached_go___redArg(x_1, x_2, x_3, x_12);
lean_dec(x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Sat_AIG_mkGateCached___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkGateCached___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Sat_AIG_mkGateCached(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
lean_object* initialize_Std_Sat_AIG_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_AIG_Lemmas(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_AIG_Cached(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_AIG_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
