// Lean compiler output
// Module: Lean.Compiler.NameMangling
// Imports: Lean.Data.Name
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
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_mk_module_initialization_function_name(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
uint32_t l_Nat_digitChar(lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* l_Nat_toDigits(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_repeatTR_loop___at_____private_Lean_Compiler_NameMangling_0__String_mangleAux_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_____private_Lean_Compiler_NameMangling_0__String_mangleAux_spec__1(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_name_mangle(lean_object*, lean_object*);
lean_object* l_List_lengthTR(lean_object*, lean_object*);
uint8_t l_instDecidableEqChar(uint32_t, uint32_t);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_String_mangle(lean_object*);
uint32_t l_Char_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Nat_repeatTR_loop___at_____private_Lean_Compiler_NameMangling_0__String_mangleAux_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 1)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint32_t x_8; lean_object* x_9; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_1, x_5);
lean_dec(x_1);
x_7 = lean_unsigned_to_nat(48u);
x_8 = l_Char_ofNat(x_7);
x_9 = lean_string_push(x_2, x_8);
x_1 = x_6;
x_2 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_____private_Lean_Compiler_NameMangling_0__String_mangleAux_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_unbox_uint32(x_3);
lean_dec(x_3);
x_6 = lean_string_push(x_1, x_5);
x_1 = x_6;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 1)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint32_t x_11; uint8_t x_17; uint8_t x_81; uint8_t x_89; lean_object* x_97; uint32_t x_98; uint8_t x_99; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_8 = x_2;
} else {
 lean_dec_ref(x_2);
 x_8 = lean_box(0);
}
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_1, x_9);
lean_dec(x_1);
x_11 = lean_string_utf8_get(x_6, x_7);
x_97 = lean_unsigned_to_nat(65u);
x_98 = lean_uint32_of_nat(x_97);
x_99 = lean_uint32_dec_le(x_98, x_11);
if (x_99 == 0)
{
x_89 = x_99;
goto block_96;
}
else
{
lean_object* x_100; uint32_t x_101; uint8_t x_102; 
x_100 = lean_unsigned_to_nat(90u);
x_101 = lean_uint32_of_nat(x_100);
x_102 = lean_uint32_dec_le(x_11, x_101);
x_89 = x_102;
goto block_96;
}
block_16:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_string_utf8_next(x_6, x_7);
lean_dec(x_7);
if (lean_is_scalar(x_8)) {
 x_13 = lean_alloc_ctor(0, 2, 0);
} else {
 x_13 = x_8;
}
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_string_push(x_3, x_11);
x_1 = x_10;
x_2 = x_13;
x_3 = x_14;
goto _start;
}
block_80:
{
if (x_17 == 0)
{
lean_object* x_18; uint32_t x_19; uint8_t x_20; 
lean_dec(x_8);
x_18 = lean_unsigned_to_nat(95u);
x_19 = l_Char_ofNat(x_18);
x_20 = l_instDecidableEqChar(x_11, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_uint32_to_nat(x_11);
x_22 = lean_unsigned_to_nat(256u);
x_23 = lean_nat_dec_lt(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_unsigned_to_nat(65536u);
x_25 = lean_nat_dec_lt(x_21, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_26 = lean_mk_string_unchecked("_U", 2, 2);
x_27 = lean_string_append(x_3, x_26);
lean_dec(x_26);
x_28 = lean_unsigned_to_nat(16u);
x_29 = l_Nat_toDigits(x_28, x_21);
x_30 = lean_unsigned_to_nat(8u);
x_31 = l_List_lengthTR(lean_box(0), x_29);
x_32 = lean_nat_sub(x_30, x_31);
lean_dec(x_31);
x_33 = l_Nat_repeatTR_loop___at_____private_Lean_Compiler_NameMangling_0__String_mangleAux_spec__0(x_32, x_27);
x_34 = l_List_foldl___at_____private_Lean_Compiler_NameMangling_0__String_mangleAux_spec__1(x_33, x_29);
x_35 = lean_string_utf8_next(x_6, x_7);
lean_dec(x_7);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_6);
lean_ctor_set(x_36, 1, x_35);
x_1 = x_10;
x_2 = x_36;
x_3 = x_34;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint32_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint32_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint32_t x_54; lean_object* x_55; lean_object* x_56; uint32_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_38 = lean_mk_string_unchecked("_u", 2, 2);
x_39 = lean_string_append(x_3, x_38);
lean_dec(x_38);
x_40 = lean_unsigned_to_nat(4096u);
x_41 = lean_unsigned_to_nat(12u);
x_42 = lean_nat_shiftr(x_21, x_41);
x_43 = l_Nat_digitChar(x_42);
lean_dec(x_42);
x_44 = lean_string_push(x_39, x_43);
x_45 = lean_nat_mod(x_21, x_40);
lean_dec(x_21);
x_46 = lean_unsigned_to_nat(8u);
x_47 = lean_nat_shiftr(x_45, x_46);
x_48 = l_Nat_digitChar(x_47);
lean_dec(x_47);
x_49 = lean_string_push(x_44, x_48);
x_50 = lean_nat_mod(x_45, x_22);
lean_dec(x_45);
x_51 = lean_unsigned_to_nat(16u);
x_52 = lean_unsigned_to_nat(4u);
x_53 = lean_nat_shiftr(x_50, x_52);
x_54 = l_Nat_digitChar(x_53);
lean_dec(x_53);
x_55 = lean_string_push(x_49, x_54);
x_56 = lean_nat_mod(x_50, x_51);
lean_dec(x_50);
x_57 = l_Nat_digitChar(x_56);
lean_dec(x_56);
x_58 = lean_string_push(x_55, x_57);
x_59 = lean_string_utf8_next(x_6, x_7);
lean_dec(x_7);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_6);
lean_ctor_set(x_60, 1, x_59);
x_1 = x_10;
x_2 = x_60;
x_3 = x_58;
goto _start;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint32_t x_67; lean_object* x_68; lean_object* x_69; uint32_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_62 = lean_mk_string_unchecked("_x", 2, 2);
x_63 = lean_string_append(x_3, x_62);
lean_dec(x_62);
x_64 = lean_unsigned_to_nat(16u);
x_65 = lean_unsigned_to_nat(4u);
x_66 = lean_nat_shiftr(x_21, x_65);
x_67 = l_Nat_digitChar(x_66);
lean_dec(x_66);
x_68 = lean_string_push(x_63, x_67);
x_69 = lean_nat_mod(x_21, x_64);
lean_dec(x_21);
x_70 = l_Nat_digitChar(x_69);
lean_dec(x_69);
x_71 = lean_string_push(x_68, x_70);
x_72 = lean_string_utf8_next(x_6, x_7);
lean_dec(x_7);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_6);
lean_ctor_set(x_73, 1, x_72);
x_1 = x_10;
x_2 = x_73;
x_3 = x_71;
goto _start;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_string_utf8_next(x_6, x_7);
lean_dec(x_7);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_6);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_mk_string_unchecked("__", 2, 2);
x_78 = lean_string_append(x_3, x_77);
lean_dec(x_77);
x_1 = x_10;
x_2 = x_76;
x_3 = x_78;
goto _start;
}
}
else
{
goto block_16;
}
}
block_88:
{
if (x_81 == 0)
{
lean_object* x_82; uint32_t x_83; uint8_t x_84; 
x_82 = lean_unsigned_to_nat(48u);
x_83 = lean_uint32_of_nat(x_82);
x_84 = lean_uint32_dec_le(x_83, x_11);
if (x_84 == 0)
{
x_17 = x_84;
goto block_80;
}
else
{
lean_object* x_85; uint32_t x_86; uint8_t x_87; 
x_85 = lean_unsigned_to_nat(57u);
x_86 = lean_uint32_of_nat(x_85);
x_87 = lean_uint32_dec_le(x_11, x_86);
x_17 = x_87;
goto block_80;
}
}
else
{
goto block_16;
}
}
block_96:
{
if (x_89 == 0)
{
lean_object* x_90; uint32_t x_91; uint8_t x_92; 
x_90 = lean_unsigned_to_nat(97u);
x_91 = lean_uint32_of_nat(x_90);
x_92 = lean_uint32_dec_le(x_91, x_11);
if (x_92 == 0)
{
x_81 = x_92;
goto block_88;
}
else
{
lean_object* x_93; uint32_t x_94; uint8_t x_95; 
x_93 = lean_unsigned_to_nat(122u);
x_94 = lean_uint32_of_nat(x_93);
x_95 = lean_uint32_dec_le(x_11, x_94);
x_81 = x_95;
goto block_88;
}
}
else
{
goto block_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_mangle(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_string_length(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_mk_string_unchecked("", 0, 0);
x_6 = l___private_Lean_Compiler_NameMangling_0__String_mangleAux(x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_mk_string_unchecked("", 0, 0);
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_String_mangle(x_4);
if (lean_obj_tag(x_3) == 0)
{
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(x_3);
x_7 = lean_mk_string_unchecked("_", 1, 1);
x_8 = lean_string_append(x_6, x_7);
lean_dec(x_7);
x_9 = lean_string_append(x_8, x_5);
lean_dec(x_5);
return x_9;
}
}
default: 
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(x_10);
x_13 = lean_mk_string_unchecked("_", 1, 1);
x_14 = lean_string_append(x_12, x_13);
x_15 = l___private_Init_Data_Repr_0__Nat_reprFast(x_11);
x_16 = lean_string_append(x_14, x_15);
lean_dec(x_15);
x_17 = lean_string_append(x_16, x_13);
lean_dec(x_13);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* lean_name_mangle(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(x_1);
x_4 = lean_string_append(x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lean_mk_module_initialization_function_name(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_mk_string_unchecked("initialize_", 11, 11);
x_3 = lean_mk_string_unchecked("", 0, 0);
x_4 = lean_name_mangle(x_1, x_3);
x_5 = lean_string_append(x_2, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* initialize_Lean_Data_Name(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_NameMangling(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Name(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
