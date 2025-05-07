// Lean compiler output
// Module: Lean.Util.PtrSet
// Imports: Init.Data.Hashable Std.Data.HashSet.Basic Std.Data.HashMap.Basic
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
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PtrMap_contains___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_mkPtrMap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqPtr(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PtrSet_contains___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPtrMap___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrSet_insert___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrSet_contains___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrMap_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_usize_to_uint64(size_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_instHashablePtr___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrMap_contains___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPtrSet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqPtr___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instBEqPtr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPtrMap___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPtrSet___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashablePtr___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrMap_insert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrMap_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPtrMap___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashablePtr(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f___redArg(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT uint8_t l_Lean_PtrSet_contains(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrSet_insert(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrSet_contains___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPtrSet___redArg(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PtrMap_contains(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_mkPtrSet___redArg___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Lean_instHashablePtr___lam__0(lean_object* x_1) {
_start:
{
size_t x_2; uint64_t x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; 
x_2 = lean_ptr_addr(x_1);
x_3 = lean_usize_to_uint64(x_2);
x_4 = lean_unsigned_to_nat(11u);
x_5 = lean_uint64_of_nat(x_4);
x_6 = lean_uint64_mix_hash(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instHashablePtr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instHashablePtr___lam__0___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instHashablePtr___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_instHashablePtr___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqPtr___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; uint8_t x_5; 
x_3 = lean_ptr_addr(x_1);
x_4 = lean_ptr_addr(x_2);
x_5 = lean_usize_dec_eq(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqPtr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instBEqPtr___lam__0___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqPtr___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_instBEqPtr___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrSet___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_shiftl(x_1, x_3);
x_5 = lean_unsigned_to_nat(3u);
x_6 = lean_nat_div(x_4, x_5);
lean_dec(x_4);
x_7 = l_Nat_nextPowerOfTwo(x_6);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_mk_array(x_7, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrSet(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkPtrSet___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrSet___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkPtrSet___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrSet___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkPtrSet(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrSet_insert___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; uint64_t x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; lean_object* x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; lean_object* x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; size_t x_20; size_t x_21; lean_object* x_22; size_t x_23; size_t x_24; size_t x_25; lean_object* x_26; uint8_t x_27; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_alloc_closure((void*)(l_Lean_instBEqPtr___lam__0___boxed), 2, 0);
x_6 = lean_array_get_size(x_4);
x_7 = lean_ptr_addr(x_2);
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
x_26 = lean_array_uget(x_4, x_25);
lean_inc(x_26);
lean_inc(x_2);
x_27 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_5, x_2, x_26);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_1);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_29 = lean_ctor_get(x_1, 1);
lean_dec(x_29);
x_30 = lean_ctor_get(x_1, 0);
lean_dec(x_30);
x_31 = lean_box(0);
x_32 = lean_nat_add(x_3, x_22);
lean_dec(x_3);
x_33 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_33, 2, x_26);
x_34 = lean_array_uset(x_4, x_25, x_33);
x_35 = lean_unsigned_to_nat(2u);
x_36 = lean_nat_shiftl(x_32, x_35);
x_37 = lean_unsigned_to_nat(3u);
x_38 = lean_nat_div(x_36, x_37);
lean_dec(x_36);
x_39 = lean_array_get_size(x_34);
x_40 = lean_nat_dec_le(x_38, x_39);
lean_dec(x_39);
lean_dec(x_38);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_alloc_closure((void*)(l_Lean_instHashablePtr___lam__0___boxed), 1, 0);
x_42 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_41, x_34);
lean_ctor_set(x_1, 1, x_42);
lean_ctor_set(x_1, 0, x_32);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_34);
lean_ctor_set(x_1, 0, x_32);
return x_1;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_1);
x_43 = lean_box(0);
x_44 = lean_nat_add(x_3, x_22);
lean_dec(x_3);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_2);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set(x_45, 2, x_26);
x_46 = lean_array_uset(x_4, x_25, x_45);
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
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_alloc_closure((void*)(l_Lean_instHashablePtr___lam__0___boxed), 1, 0);
x_54 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_53, x_46);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_44);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_44);
lean_ctor_set(x_56, 1, x_46);
return x_56;
}
}
}
else
{
lean_dec(x_26);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PtrSet_insert(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; uint64_t x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; lean_object* x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; size_t x_21; size_t x_22; lean_object* x_23; size_t x_24; size_t x_25; size_t x_26; lean_object* x_27; uint8_t x_28; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_Lean_instBEqPtr___lam__0___boxed), 2, 0);
x_7 = lean_array_get_size(x_5);
x_8 = lean_ptr_addr(x_3);
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
x_27 = lean_array_uget(x_5, x_26);
lean_inc(x_27);
lean_inc(x_3);
x_28 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_6, x_3, x_27);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_2);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_30 = lean_ctor_get(x_2, 1);
lean_dec(x_30);
x_31 = lean_ctor_get(x_2, 0);
lean_dec(x_31);
x_32 = lean_box(0);
x_33 = lean_nat_add(x_4, x_23);
lean_dec(x_4);
x_34 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_34, 0, x_3);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_27);
x_35 = lean_array_uset(x_5, x_26, x_34);
x_36 = lean_unsigned_to_nat(2u);
x_37 = lean_nat_shiftl(x_33, x_36);
x_38 = lean_unsigned_to_nat(3u);
x_39 = lean_nat_div(x_37, x_38);
lean_dec(x_37);
x_40 = lean_array_get_size(x_35);
x_41 = lean_nat_dec_le(x_39, x_40);
lean_dec(x_40);
lean_dec(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_alloc_closure((void*)(l_Lean_instHashablePtr___lam__0___boxed), 1, 0);
x_43 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_42, x_35);
lean_ctor_set(x_2, 1, x_43);
lean_ctor_set(x_2, 0, x_33);
return x_2;
}
else
{
lean_ctor_set(x_2, 1, x_35);
lean_ctor_set(x_2, 0, x_33);
return x_2;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
lean_dec(x_2);
x_44 = lean_box(0);
x_45 = lean_nat_add(x_4, x_23);
lean_dec(x_4);
x_46 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_46, 0, x_3);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_46, 2, x_27);
x_47 = lean_array_uset(x_5, x_26, x_46);
x_48 = lean_unsigned_to_nat(2u);
x_49 = lean_nat_shiftl(x_45, x_48);
x_50 = lean_unsigned_to_nat(3u);
x_51 = lean_nat_div(x_49, x_50);
lean_dec(x_49);
x_52 = lean_array_get_size(x_47);
x_53 = lean_nat_dec_le(x_51, x_52);
lean_dec(x_52);
lean_dec(x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_alloc_closure((void*)(l_Lean_instHashablePtr___lam__0___boxed), 1, 0);
x_55 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_54, x_47);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_45);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_45);
lean_ctor_set(x_57, 1, x_47);
return x_57;
}
}
}
else
{
lean_dec(x_27);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PtrSet_contains___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; uint64_t x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; lean_object* x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; size_t x_19; size_t x_20; lean_object* x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_alloc_closure((void*)(l_Lean_instBEqPtr___lam__0___boxed), 2, 0);
x_5 = lean_array_get_size(x_3);
x_6 = lean_ptr_addr(x_2);
x_7 = lean_usize_to_uint64(x_6);
x_8 = lean_unsigned_to_nat(11u);
x_9 = lean_uint64_of_nat(x_8);
x_10 = lean_uint64_mix_hash(x_7, x_9);
x_11 = lean_unsigned_to_nat(32u);
x_12 = lean_uint64_of_nat(x_11);
x_13 = lean_uint64_shift_right(x_10, x_12);
x_14 = lean_uint64_xor(x_10, x_13);
x_15 = lean_unsigned_to_nat(16u);
x_16 = lean_uint64_of_nat(x_15);
x_17 = lean_uint64_shift_right(x_14, x_16);
x_18 = lean_uint64_xor(x_14, x_17);
x_19 = lean_uint64_to_usize(x_18);
x_20 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_usize_of_nat(x_21);
x_23 = lean_usize_sub(x_20, x_22);
x_24 = lean_usize_land(x_19, x_23);
x_25 = lean_array_uget(x_3, x_24);
x_26 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_4, x_2, x_25);
return x_26;
}
}
LEAN_EXPORT uint8_t l_Lean_PtrSet_contains(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; uint64_t x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; lean_object* x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; lean_object* x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; size_t x_20; size_t x_21; lean_object* x_22; size_t x_23; size_t x_24; size_t x_25; lean_object* x_26; uint8_t x_27; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_alloc_closure((void*)(l_Lean_instBEqPtr___lam__0___boxed), 2, 0);
x_6 = lean_array_get_size(x_4);
x_7 = lean_ptr_addr(x_3);
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
x_26 = lean_array_uget(x_4, x_25);
x_27 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_5, x_3, x_26);
return x_27;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrSet_contains___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PtrSet_contains___redArg(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrSet_contains___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PtrSet_contains(x_1, x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrMap___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_shiftl(x_1, x_3);
x_5 = lean_unsigned_to_nat(3u);
x_6 = lean_nat_div(x_4, x_5);
lean_dec(x_4);
x_7 = l_Nat_nextPowerOfTwo(x_6);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_mk_array(x_7, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrMap(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_mkPtrMap___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrMap___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkPtrMap___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrMap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_mkPtrMap(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_insert___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; uint64_t x_10; lean_object* x_11; uint64_t x_12; uint64_t x_13; lean_object* x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; lean_object* x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; size_t x_22; size_t x_23; lean_object* x_24; size_t x_25; size_t x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_alloc_closure((void*)(l_Lean_instBEqPtr___lam__0___boxed), 2, 0);
x_8 = lean_array_get_size(x_6);
x_9 = lean_ptr_addr(x_2);
x_10 = lean_usize_to_uint64(x_9);
x_11 = lean_unsigned_to_nat(11u);
x_12 = lean_uint64_of_nat(x_11);
x_13 = lean_uint64_mix_hash(x_10, x_12);
x_14 = lean_unsigned_to_nat(32u);
x_15 = lean_uint64_of_nat(x_14);
x_16 = lean_uint64_shift_right(x_13, x_15);
x_17 = lean_uint64_xor(x_13, x_16);
x_18 = lean_unsigned_to_nat(16u);
x_19 = lean_uint64_of_nat(x_18);
x_20 = lean_uint64_shift_right(x_17, x_19);
x_21 = lean_uint64_xor(x_17, x_20);
x_22 = lean_uint64_to_usize(x_21);
x_23 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_usize_of_nat(x_24);
x_26 = lean_usize_sub(x_23, x_25);
x_27 = lean_usize_land(x_22, x_26);
x_28 = lean_array_uget(x_6, x_27);
lean_inc(x_28);
lean_inc(x_2);
lean_inc(x_7);
x_29 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_7, x_2, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_7);
x_30 = lean_nat_add(x_5, x_24);
lean_dec(x_5);
x_31 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_3);
lean_ctor_set(x_31, 2, x_28);
x_32 = lean_array_uset(x_6, x_27, x_31);
x_33 = lean_unsigned_to_nat(2u);
x_34 = lean_nat_shiftl(x_30, x_33);
x_35 = lean_unsigned_to_nat(3u);
x_36 = lean_nat_div(x_34, x_35);
lean_dec(x_34);
x_37 = lean_array_get_size(x_32);
x_38 = lean_nat_dec_le(x_36, x_37);
lean_dec(x_37);
lean_dec(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_alloc_closure((void*)(l_Lean_instHashablePtr___lam__0___boxed), 1, 0);
x_40 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_39, x_32);
lean_ctor_set(x_1, 1, x_40);
lean_ctor_set(x_1, 0, x_30);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_32);
lean_ctor_set(x_1, 0, x_30);
return x_1;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_box(0);
x_42 = lean_array_uset(x_6, x_27, x_41);
x_43 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_7, x_2, x_3, x_28);
x_44 = lean_array_uset(x_42, x_27, x_43);
lean_ctor_set(x_1, 1, x_44);
return x_1;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; size_t x_49; uint64_t x_50; lean_object* x_51; uint64_t x_52; uint64_t x_53; lean_object* x_54; uint64_t x_55; uint64_t x_56; uint64_t x_57; lean_object* x_58; uint64_t x_59; uint64_t x_60; uint64_t x_61; size_t x_62; size_t x_63; lean_object* x_64; size_t x_65; size_t x_66; size_t x_67; lean_object* x_68; uint8_t x_69; 
x_45 = lean_ctor_get(x_1, 0);
x_46 = lean_ctor_get(x_1, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_1);
x_47 = lean_alloc_closure((void*)(l_Lean_instBEqPtr___lam__0___boxed), 2, 0);
x_48 = lean_array_get_size(x_46);
x_49 = lean_ptr_addr(x_2);
x_50 = lean_usize_to_uint64(x_49);
x_51 = lean_unsigned_to_nat(11u);
x_52 = lean_uint64_of_nat(x_51);
x_53 = lean_uint64_mix_hash(x_50, x_52);
x_54 = lean_unsigned_to_nat(32u);
x_55 = lean_uint64_of_nat(x_54);
x_56 = lean_uint64_shift_right(x_53, x_55);
x_57 = lean_uint64_xor(x_53, x_56);
x_58 = lean_unsigned_to_nat(16u);
x_59 = lean_uint64_of_nat(x_58);
x_60 = lean_uint64_shift_right(x_57, x_59);
x_61 = lean_uint64_xor(x_57, x_60);
x_62 = lean_uint64_to_usize(x_61);
x_63 = lean_usize_of_nat(x_48);
lean_dec(x_48);
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_usize_of_nat(x_64);
x_66 = lean_usize_sub(x_63, x_65);
x_67 = lean_usize_land(x_62, x_66);
x_68 = lean_array_uget(x_46, x_67);
lean_inc(x_68);
lean_inc(x_2);
lean_inc(x_47);
x_69 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_47, x_2, x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
lean_dec(x_47);
x_70 = lean_nat_add(x_45, x_64);
lean_dec(x_45);
x_71 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_71, 0, x_2);
lean_ctor_set(x_71, 1, x_3);
lean_ctor_set(x_71, 2, x_68);
x_72 = lean_array_uset(x_46, x_67, x_71);
x_73 = lean_unsigned_to_nat(2u);
x_74 = lean_nat_shiftl(x_70, x_73);
x_75 = lean_unsigned_to_nat(3u);
x_76 = lean_nat_div(x_74, x_75);
lean_dec(x_74);
x_77 = lean_array_get_size(x_72);
x_78 = lean_nat_dec_le(x_76, x_77);
lean_dec(x_77);
lean_dec(x_76);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_alloc_closure((void*)(l_Lean_instHashablePtr___lam__0___boxed), 1, 0);
x_80 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_79, x_72);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_70);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_70);
lean_ctor_set(x_82, 1, x_72);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_83 = lean_box(0);
x_84 = lean_array_uset(x_46, x_67, x_83);
x_85 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_47, x_2, x_3, x_68);
x_86 = lean_array_uset(x_84, x_67, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_45);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_insert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; uint64_t x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; lean_object* x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; lean_object* x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; size_t x_24; size_t x_25; lean_object* x_26; size_t x_27; size_t x_28; size_t x_29; lean_object* x_30; uint8_t x_31; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_alloc_closure((void*)(l_Lean_instBEqPtr___lam__0___boxed), 2, 0);
x_10 = lean_array_get_size(x_8);
x_11 = lean_ptr_addr(x_4);
x_12 = lean_usize_to_uint64(x_11);
x_13 = lean_unsigned_to_nat(11u);
x_14 = lean_uint64_of_nat(x_13);
x_15 = lean_uint64_mix_hash(x_12, x_14);
x_16 = lean_unsigned_to_nat(32u);
x_17 = lean_uint64_of_nat(x_16);
x_18 = lean_uint64_shift_right(x_15, x_17);
x_19 = lean_uint64_xor(x_15, x_18);
x_20 = lean_unsigned_to_nat(16u);
x_21 = lean_uint64_of_nat(x_20);
x_22 = lean_uint64_shift_right(x_19, x_21);
x_23 = lean_uint64_xor(x_19, x_22);
x_24 = lean_uint64_to_usize(x_23);
x_25 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_usize_of_nat(x_26);
x_28 = lean_usize_sub(x_25, x_27);
x_29 = lean_usize_land(x_24, x_28);
x_30 = lean_array_uget(x_8, x_29);
lean_inc(x_30);
lean_inc(x_4);
lean_inc(x_9);
x_31 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_9, x_4, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_dec(x_9);
x_32 = lean_nat_add(x_7, x_26);
lean_dec(x_7);
x_33 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_5);
lean_ctor_set(x_33, 2, x_30);
x_34 = lean_array_uset(x_8, x_29, x_33);
x_35 = lean_unsigned_to_nat(2u);
x_36 = lean_nat_shiftl(x_32, x_35);
x_37 = lean_unsigned_to_nat(3u);
x_38 = lean_nat_div(x_36, x_37);
lean_dec(x_36);
x_39 = lean_array_get_size(x_34);
x_40 = lean_nat_dec_le(x_38, x_39);
lean_dec(x_39);
lean_dec(x_38);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_alloc_closure((void*)(l_Lean_instHashablePtr___lam__0___boxed), 1, 0);
x_42 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_41, x_34);
lean_ctor_set(x_3, 1, x_42);
lean_ctor_set(x_3, 0, x_32);
return x_3;
}
else
{
lean_ctor_set(x_3, 1, x_34);
lean_ctor_set(x_3, 0, x_32);
return x_3;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_box(0);
x_44 = lean_array_uset(x_8, x_29, x_43);
x_45 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_9, x_4, x_5, x_30);
x_46 = lean_array_uset(x_44, x_29, x_45);
lean_ctor_set(x_3, 1, x_46);
return x_3;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; size_t x_51; uint64_t x_52; lean_object* x_53; uint64_t x_54; uint64_t x_55; lean_object* x_56; uint64_t x_57; uint64_t x_58; uint64_t x_59; lean_object* x_60; uint64_t x_61; uint64_t x_62; uint64_t x_63; size_t x_64; size_t x_65; lean_object* x_66; size_t x_67; size_t x_68; size_t x_69; lean_object* x_70; uint8_t x_71; 
x_47 = lean_ctor_get(x_3, 0);
x_48 = lean_ctor_get(x_3, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_3);
x_49 = lean_alloc_closure((void*)(l_Lean_instBEqPtr___lam__0___boxed), 2, 0);
x_50 = lean_array_get_size(x_48);
x_51 = lean_ptr_addr(x_4);
x_52 = lean_usize_to_uint64(x_51);
x_53 = lean_unsigned_to_nat(11u);
x_54 = lean_uint64_of_nat(x_53);
x_55 = lean_uint64_mix_hash(x_52, x_54);
x_56 = lean_unsigned_to_nat(32u);
x_57 = lean_uint64_of_nat(x_56);
x_58 = lean_uint64_shift_right(x_55, x_57);
x_59 = lean_uint64_xor(x_55, x_58);
x_60 = lean_unsigned_to_nat(16u);
x_61 = lean_uint64_of_nat(x_60);
x_62 = lean_uint64_shift_right(x_59, x_61);
x_63 = lean_uint64_xor(x_59, x_62);
x_64 = lean_uint64_to_usize(x_63);
x_65 = lean_usize_of_nat(x_50);
lean_dec(x_50);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_usize_of_nat(x_66);
x_68 = lean_usize_sub(x_65, x_67);
x_69 = lean_usize_land(x_64, x_68);
x_70 = lean_array_uget(x_48, x_69);
lean_inc(x_70);
lean_inc(x_4);
lean_inc(x_49);
x_71 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_49, x_4, x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
lean_dec(x_49);
x_72 = lean_nat_add(x_47, x_66);
lean_dec(x_47);
x_73 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_73, 0, x_4);
lean_ctor_set(x_73, 1, x_5);
lean_ctor_set(x_73, 2, x_70);
x_74 = lean_array_uset(x_48, x_69, x_73);
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
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_alloc_closure((void*)(l_Lean_instHashablePtr___lam__0___boxed), 1, 0);
x_82 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_81, x_74);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_72);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_72);
lean_ctor_set(x_84, 1, x_74);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_box(0);
x_86 = lean_array_uset(x_48, x_69, x_85);
x_87 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_49, x_4, x_5, x_70);
x_88 = lean_array_uset(x_86, x_69, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_47);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PtrMap_contains___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; uint64_t x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; lean_object* x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; size_t x_19; size_t x_20; lean_object* x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_alloc_closure((void*)(l_Lean_instBEqPtr___lam__0___boxed), 2, 0);
x_5 = lean_array_get_size(x_3);
x_6 = lean_ptr_addr(x_2);
x_7 = lean_usize_to_uint64(x_6);
x_8 = lean_unsigned_to_nat(11u);
x_9 = lean_uint64_of_nat(x_8);
x_10 = lean_uint64_mix_hash(x_7, x_9);
x_11 = lean_unsigned_to_nat(32u);
x_12 = lean_uint64_of_nat(x_11);
x_13 = lean_uint64_shift_right(x_10, x_12);
x_14 = lean_uint64_xor(x_10, x_13);
x_15 = lean_unsigned_to_nat(16u);
x_16 = lean_uint64_of_nat(x_15);
x_17 = lean_uint64_shift_right(x_14, x_16);
x_18 = lean_uint64_xor(x_14, x_17);
x_19 = lean_uint64_to_usize(x_18);
x_20 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_usize_of_nat(x_21);
x_23 = lean_usize_sub(x_20, x_22);
x_24 = lean_usize_land(x_19, x_23);
x_25 = lean_array_uget(x_3, x_24);
x_26 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_4, x_2, x_25);
return x_26;
}
}
LEAN_EXPORT uint8_t l_Lean_PtrMap_contains(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; uint64_t x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; lean_object* x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; size_t x_21; size_t x_22; lean_object* x_23; size_t x_24; size_t x_25; size_t x_26; lean_object* x_27; uint8_t x_28; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_alloc_closure((void*)(l_Lean_instBEqPtr___lam__0___boxed), 2, 0);
x_7 = lean_array_get_size(x_5);
x_8 = lean_ptr_addr(x_4);
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
x_27 = lean_array_uget(x_5, x_26);
x_28 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_6, x_4, x_27);
return x_28;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_contains___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PtrMap_contains___redArg(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_contains___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lean_PtrMap_contains(x_1, x_2, x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; uint64_t x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; lean_object* x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; size_t x_19; size_t x_20; lean_object* x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_alloc_closure((void*)(l_Lean_instBEqPtr___lam__0___boxed), 2, 0);
x_5 = lean_array_get_size(x_3);
x_6 = lean_ptr_addr(x_2);
x_7 = lean_usize_to_uint64(x_6);
x_8 = lean_unsigned_to_nat(11u);
x_9 = lean_uint64_of_nat(x_8);
x_10 = lean_uint64_mix_hash(x_7, x_9);
x_11 = lean_unsigned_to_nat(32u);
x_12 = lean_uint64_of_nat(x_11);
x_13 = lean_uint64_shift_right(x_10, x_12);
x_14 = lean_uint64_xor(x_10, x_13);
x_15 = lean_unsigned_to_nat(16u);
x_16 = lean_uint64_of_nat(x_15);
x_17 = lean_uint64_shift_right(x_14, x_16);
x_18 = lean_uint64_xor(x_14, x_17);
x_19 = lean_uint64_to_usize(x_18);
x_20 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_usize_of_nat(x_21);
x_23 = lean_usize_sub(x_20, x_22);
x_24 = lean_usize_land(x_19, x_23);
x_25 = lean_array_uget(x_3, x_24);
x_26 = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(x_4, x_2, x_25);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; uint64_t x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; lean_object* x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; size_t x_21; size_t x_22; lean_object* x_23; size_t x_24; size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_alloc_closure((void*)(l_Lean_instBEqPtr___lam__0___boxed), 2, 0);
x_7 = lean_array_get_size(x_5);
x_8 = lean_ptr_addr(x_4);
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
x_27 = lean_array_uget(x_5, x_26);
x_28 = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(x_6, x_4, x_27);
return x_28;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PtrMap_find_x3f___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PtrMap_find_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* initialize_Init_Data_Hashable(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_HashSet_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_HashMap_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_PtrSet(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Hashable(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashSet_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
