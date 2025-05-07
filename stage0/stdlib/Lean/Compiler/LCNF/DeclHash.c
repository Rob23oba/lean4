// Lean compiler output
// Module: Lean.Compiler.LCNF.DeclHash
// Imports: Lean.Compiler.LCNF.Basic
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_hashParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashAlt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashAlts___boxed(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableCode___lam__0(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashParams___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_DeclHash_0__Lean_Compiler_LCNF_hashDeclValue____x40_Lean_Compiler_LCNF_DeclHash___hyg_273____boxed(lean_object*);
LEAN_EXPORT uint64_t l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_hashAlts_spec__0(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashParams(lean_object*);
uint64_t l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hashInlineAttributeKind____x40_Lean_Compiler_InlineAttrs___hyg_36_(uint8_t);
uint64_t l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableParam___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableCode___lam__0___boxed(lean_object*);
LEAN_EXPORT uint64_t l___private_Lean_Compiler_LCNF_DeclHash_0__Lean_Compiler_LCNF_hashDeclValue____x40_Lean_Compiler_LCNF_DeclHash___hyg_273_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDecl;
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashCode(lean_object*);
uint64_t l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_hashLetValue____x40_Lean_Compiler_LCNF_Basic___hyg_1088__spec__0(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_hashAlts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableDeclValue;
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_____private_Lean_Compiler_LCNF_DeclHash_0__Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_319__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashCode___boxed(lean_object*);
LEAN_EXPORT uint64_t l_List_foldl___at_____private_Lean_Compiler_LCNF_DeclHash_0__Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_319__spec__0(uint64_t, lean_object*);
LEAN_EXPORT uint64_t l___private_Lean_Compiler_LCNF_DeclHash_0__Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_319_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableCode;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint64_t l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_hashLetValue____x40_Lean_Compiler_LCNF_Basic___hyg_1088_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashAlt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableParam;
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_DeclHash_0__Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_319____boxed(lean_object*);
LEAN_EXPORT uint64_t l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_hashParams_spec__0(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashAlts(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableParam___lam__0___boxed(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint64_t l___private_Lean_Compiler_ExternAttr_0__Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_456_(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableParam___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint64_t x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_2);
x_4 = lean_ctor_get(x_1, 2);
x_5 = l_Lean_Expr_hash(x_4);
x_6 = lean_uint64_mix_hash(x_3, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instHashableParam() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instHashableParam___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableParam___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_instHashableParam___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_hashParams_spec__0(lean_object* x_1, size_t x_2, size_t x_3, uint64_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; lean_object* x_13; size_t x_14; size_t x_15; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_7);
lean_dec(x_7);
x_9 = lean_ctor_get(x_6, 2);
lean_inc(x_9);
lean_dec(x_6);
x_10 = l_Lean_Expr_hash(x_9);
lean_dec(x_9);
x_11 = lean_uint64_mix_hash(x_8, x_10);
x_12 = lean_uint64_mix_hash(x_4, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_usize_of_nat(x_13);
x_15 = lean_usize_add(x_2, x_14);
x_2 = x_15;
x_4 = x_12;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashParams(lean_object* x_1) {
_start:
{
lean_object* x_2; uint64_t x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_unsigned_to_nat(7u);
x_3 = lean_uint64_of_nat(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_dec(x_5);
return x_3;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_5);
if (x_7 == 0)
{
lean_dec(x_5);
return x_3;
}
else
{
size_t x_8; size_t x_9; uint64_t x_10; 
x_8 = lean_usize_of_nat(x_4);
x_9 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_10 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_hashParams_spec__0(x_1, x_8, x_9, x_3);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_hashParams_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_hashParams_spec__0(x_1, x_5, x_6, x_7);
lean_dec(x_1);
x_9 = lean_box_uint64(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashParams___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_hashParams(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashAlt(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = l_Lean_Name_hash___override(x_2);
x_11 = lean_unsigned_to_nat(7u);
x_12 = lean_uint64_of_nat(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_get_size(x_3);
x_15 = lean_nat_dec_lt(x_13, x_14);
if (x_15 == 0)
{
lean_dec(x_14);
x_6 = x_12;
goto block_10;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_14, x_14);
if (x_16 == 0)
{
lean_dec(x_14);
x_6 = x_12;
goto block_10;
}
else
{
size_t x_17; size_t x_18; uint64_t x_19; 
x_17 = lean_usize_of_nat(x_13);
x_18 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_19 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_hashParams_spec__0(x_3, x_17, x_18, x_12);
x_6 = x_19;
goto block_10;
}
}
block_10:
{
uint64_t x_7; uint64_t x_8; uint64_t x_9; 
x_7 = lean_uint64_mix_hash(x_5, x_6);
x_8 = l_Lean_Compiler_LCNF_hashCode(x_4);
x_9 = lean_uint64_mix_hash(x_7, x_8);
return x_9;
}
}
else
{
lean_object* x_20; uint64_t x_21; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = l_Lean_Compiler_LCNF_hashCode(x_20);
return x_21;
}
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashCode(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint64_t x_31; lean_object* x_32; uint64_t x_33; uint64_t x_34; lean_object* x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_ctor_get(x_1, 1);
x_30 = lean_ctor_get(x_28, 0);
x_31 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_30);
x_32 = lean_ctor_get(x_28, 2);
x_33 = l_Lean_Expr_hash(x_32);
x_34 = lean_uint64_mix_hash(x_31, x_33);
x_35 = lean_ctor_get(x_28, 3);
x_36 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_hashLetValue____x40_Lean_Compiler_LCNF_Basic___hyg_1088_(x_35);
x_37 = l_Lean_Compiler_LCNF_hashCode(x_29);
x_38 = lean_uint64_mix_hash(x_36, x_37);
x_39 = lean_uint64_mix_hash(x_34, x_38);
return x_39;
}
case 3:
{
lean_object* x_40; lean_object* x_41; uint64_t x_42; lean_object* x_43; uint64_t x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_40 = lean_ctor_get(x_1, 0);
x_41 = lean_ctor_get(x_1, 1);
x_42 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_40);
x_43 = lean_unsigned_to_nat(7u);
x_44 = lean_uint64_of_nat(x_43);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_array_get_size(x_41);
x_47 = lean_nat_dec_lt(x_45, x_46);
if (x_47 == 0)
{
uint64_t x_48; 
lean_dec(x_46);
x_48 = lean_uint64_mix_hash(x_42, x_44);
return x_48;
}
else
{
uint8_t x_49; 
x_49 = lean_nat_dec_le(x_46, x_46);
if (x_49 == 0)
{
uint64_t x_50; 
lean_dec(x_46);
x_50 = lean_uint64_mix_hash(x_42, x_44);
return x_50;
}
else
{
size_t x_51; size_t x_52; uint64_t x_53; uint64_t x_54; 
x_51 = lean_usize_of_nat(x_45);
x_52 = lean_usize_of_nat(x_46);
lean_dec(x_46);
x_53 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_hashLetValue____x40_Lean_Compiler_LCNF_Basic___hyg_1088__spec__0(x_41, x_51, x_52, x_44);
x_54 = lean_uint64_mix_hash(x_42, x_53);
return x_54;
}
}
}
case 4:
{
lean_object* x_55; lean_object* x_56; uint64_t x_57; lean_object* x_58; uint64_t x_59; uint64_t x_60; lean_object* x_61; uint64_t x_62; uint64_t x_63; 
x_55 = lean_ctor_get(x_1, 0);
x_56 = lean_ctor_get(x_55, 2);
x_57 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_56);
x_58 = lean_ctor_get(x_55, 1);
x_59 = l_Lean_Expr_hash(x_58);
x_60 = lean_uint64_mix_hash(x_57, x_59);
x_61 = lean_ctor_get(x_55, 3);
x_62 = l_Lean_Compiler_LCNF_hashAlts(x_61);
x_63 = lean_uint64_mix_hash(x_60, x_62);
return x_63;
}
case 5:
{
lean_object* x_64; uint64_t x_65; 
x_64 = lean_ctor_get(x_1, 0);
x_65 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_64);
return x_65;
}
case 6:
{
lean_object* x_66; uint64_t x_67; 
x_66 = lean_ctor_get(x_1, 0);
x_67 = l_Lean_Expr_hash(x_66);
return x_67;
}
default: 
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_1, 0);
x_69 = lean_ctor_get(x_1, 1);
x_2 = x_68;
x_3 = x_69;
goto block_27;
}
}
block_27:
{
lean_object* x_4; uint64_t x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_4);
x_6 = lean_ctor_get(x_2, 3);
x_7 = l_Lean_Expr_hash(x_6);
x_8 = lean_uint64_mix_hash(x_5, x_7);
x_9 = lean_ctor_get(x_2, 4);
x_10 = l_Lean_Compiler_LCNF_hashCode(x_9);
x_11 = l_Lean_Compiler_LCNF_hashCode(x_3);
x_12 = lean_uint64_mix_hash(x_10, x_11);
x_13 = lean_uint64_mix_hash(x_8, x_12);
x_14 = lean_ctor_get(x_2, 2);
x_15 = lean_unsigned_to_nat(7u);
x_16 = lean_uint64_of_nat(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_get_size(x_14);
x_19 = lean_nat_dec_lt(x_17, x_18);
if (x_19 == 0)
{
uint64_t x_20; 
lean_dec(x_18);
x_20 = lean_uint64_mix_hash(x_13, x_16);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_18, x_18);
if (x_21 == 0)
{
uint64_t x_22; 
lean_dec(x_18);
x_22 = lean_uint64_mix_hash(x_13, x_16);
return x_22;
}
else
{
size_t x_23; size_t x_24; uint64_t x_25; uint64_t x_26; 
x_23 = lean_usize_of_nat(x_17);
x_24 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_25 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_hashParams_spec__0(x_14, x_23, x_24, x_16);
x_26 = lean_uint64_mix_hash(x_13, x_25);
return x_26;
}
}
}
}
}
LEAN_EXPORT uint64_t l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_hashAlts_spec__0(lean_object* x_1, size_t x_2, size_t x_3, uint64_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Compiler_LCNF_hashAlt(x_6);
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
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_hashAlts(lean_object* x_1) {
_start:
{
lean_object* x_2; uint64_t x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_unsigned_to_nat(7u);
x_3 = lean_uint64_of_nat(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_dec(x_5);
return x_3;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_5);
if (x_7 == 0)
{
lean_dec(x_5);
return x_3;
}
else
{
size_t x_8; size_t x_9; uint64_t x_10; 
x_8 = lean_usize_of_nat(x_4);
x_9 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_10 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_hashAlts_spec__0(x_1, x_8, x_9, x_3);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashAlt___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_hashAlt(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashCode___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_hashCode(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_hashAlts_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_hashAlts_spec__0(x_1, x_5, x_6, x_7);
lean_dec(x_1);
x_9 = lean_box_uint64(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hashAlts___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_hashAlts(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableCode___lam__0(lean_object* x_1) {
_start:
{
uint64_t x_2; 
x_2 = l_Lean_Compiler_LCNF_hashCode(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instHashableCode() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instHashableCode___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableCode___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_instHashableCode___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Compiler_LCNF_DeclHash_0__Lean_Compiler_LCNF_hashDeclValue____x40_Lean_Compiler_LCNF_DeclHash___hyg_273_(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_uint64_of_nat(x_3);
x_5 = l_Lean_Compiler_LCNF_hashCode(x_2);
x_6 = lean_uint64_mix_hash(x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_uint64_of_nat(x_8);
x_10 = l___private_Lean_Compiler_ExternAttr_0__Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_456_(x_7);
x_11 = lean_uint64_mix_hash(x_9, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_DeclHash_0__Lean_Compiler_LCNF_hashDeclValue____x40_Lean_Compiler_LCNF_DeclHash___hyg_273____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Compiler_LCNF_DeclHash_0__Lean_Compiler_LCNF_hashDeclValue____x40_Lean_Compiler_LCNF_DeclHash___hyg_273_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instHashableDeclValue() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_DeclHash_0__Lean_Compiler_LCNF_hashDeclValue____x40_Lean_Compiler_LCNF_DeclHash___hyg_273____boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at_____private_Lean_Compiler_LCNF_DeclHash_0__Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_319__spec__0(uint64_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_Name_hash___override(x_3);
x_6 = lean_uint64_mix_hash(x_1, x_5);
x_1 = x_6;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT uint64_t l___private_Lean_Compiler_LCNF_DeclHash_0__Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_319_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_24; uint64_t x_25; lean_object* x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; lean_object* x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; lean_object* x_51; uint8_t x_52; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 4);
lean_inc(x_6);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_9 = lean_ctor_get(x_1, 5);
lean_inc(x_9);
lean_dec(x_1);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_uint64_of_nat(x_32);
x_34 = l_Lean_Name_hash___override(x_2);
lean_dec(x_2);
x_35 = lean_uint64_mix_hash(x_33, x_34);
x_36 = lean_unsigned_to_nat(7u);
x_37 = lean_uint64_of_nat(x_36);
x_38 = l_List_foldl___at_____private_Lean_Compiler_LCNF_DeclHash_0__Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_319__spec__0(x_37, x_3);
lean_dec(x_3);
x_39 = lean_uint64_mix_hash(x_35, x_38);
x_40 = l_Lean_Expr_hash(x_4);
lean_dec(x_4);
x_41 = lean_uint64_mix_hash(x_39, x_40);
x_51 = lean_array_get_size(x_5);
x_52 = lean_nat_dec_lt(x_32, x_51);
if (x_52 == 0)
{
lean_dec(x_51);
lean_dec(x_5);
x_42 = x_37;
goto block_50;
}
else
{
uint8_t x_53; 
x_53 = lean_nat_dec_le(x_51, x_51);
if (x_53 == 0)
{
lean_dec(x_51);
lean_dec(x_5);
x_42 = x_37;
goto block_50;
}
else
{
size_t x_54; size_t x_55; uint64_t x_56; 
x_54 = lean_usize_of_nat(x_32);
x_55 = lean_usize_of_nat(x_51);
lean_dec(x_51);
x_56 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_hashParams_spec__0(x_5, x_54, x_55, x_37);
lean_dec(x_5);
x_42 = x_56;
goto block_50;
}
}
block_23:
{
uint64_t x_12; 
x_12 = lean_uint64_mix_hash(x_10, x_11);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_13; uint64_t x_14; uint64_t x_15; 
x_13 = lean_unsigned_to_nat(11u);
x_14 = lean_uint64_of_nat(x_13);
x_15 = lean_uint64_mix_hash(x_12, x_14);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; uint64_t x_18; lean_object* x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; 
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
x_18 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hashInlineAttributeKind____x40_Lean_Compiler_InlineAttrs___hyg_36_(x_17);
x_19 = lean_unsigned_to_nat(13u);
x_20 = lean_uint64_of_nat(x_19);
x_21 = lean_uint64_mix_hash(x_18, x_20);
x_22 = lean_uint64_mix_hash(x_12, x_21);
return x_22;
}
}
block_31:
{
uint64_t x_26; 
x_26 = lean_uint64_mix_hash(x_24, x_25);
if (x_8 == 0)
{
lean_object* x_27; uint64_t x_28; 
x_27 = lean_unsigned_to_nat(13u);
x_28 = lean_uint64_of_nat(x_27);
x_10 = x_26;
x_11 = x_28;
goto block_23;
}
else
{
lean_object* x_29; uint64_t x_30; 
x_29 = lean_unsigned_to_nat(11u);
x_30 = lean_uint64_of_nat(x_29);
x_10 = x_26;
x_11 = x_30;
goto block_23;
}
}
block_50:
{
uint64_t x_43; uint64_t x_44; uint64_t x_45; 
x_43 = lean_uint64_mix_hash(x_41, x_42);
x_44 = l___private_Lean_Compiler_LCNF_DeclHash_0__Lean_Compiler_LCNF_hashDeclValue____x40_Lean_Compiler_LCNF_DeclHash___hyg_273_(x_6);
lean_dec(x_6);
x_45 = lean_uint64_mix_hash(x_43, x_44);
if (x_7 == 0)
{
lean_object* x_46; uint64_t x_47; 
x_46 = lean_unsigned_to_nat(13u);
x_47 = lean_uint64_of_nat(x_46);
x_24 = x_45;
x_25 = x_47;
goto block_31;
}
else
{
lean_object* x_48; uint64_t x_49; 
x_48 = lean_unsigned_to_nat(11u);
x_49 = lean_uint64_of_nat(x_48);
x_24 = x_45;
x_25 = x_49;
goto block_31;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_____private_Lean_Compiler_LCNF_DeclHash_0__Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_319__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_List_foldl___at_____private_Lean_Compiler_LCNF_DeclHash_0__Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_319__spec__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_DeclHash_0__Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_319____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Compiler_LCNF_DeclHash_0__Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_319_(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instHashableDecl() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_DeclHash_0__Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_319____boxed), 1, 0);
return x_1;
}
}
lean_object* initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_DeclHash(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_instHashableParam = _init_l_Lean_Compiler_LCNF_instHashableParam();
lean_mark_persistent(l_Lean_Compiler_LCNF_instHashableParam);
l_Lean_Compiler_LCNF_instHashableCode = _init_l_Lean_Compiler_LCNF_instHashableCode();
lean_mark_persistent(l_Lean_Compiler_LCNF_instHashableCode);
l_Lean_Compiler_LCNF_instHashableDeclValue = _init_l_Lean_Compiler_LCNF_instHashableDeclValue();
lean_mark_persistent(l_Lean_Compiler_LCNF_instHashableDeclValue);
l_Lean_Compiler_LCNF_instHashableDecl = _init_l_Lean_Compiler_LCNF_instHashableDecl();
lean_mark_persistent(l_Lean_Compiler_LCNF_instHashableDecl);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
