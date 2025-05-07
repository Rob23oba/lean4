// Lean compiler output
// Module: Init.Data.Format.Syntax
// Imports: Init.Data.Format.Macro Init.Data.Format.Instances Init.Meta
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_formatStxAux___lam__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_formatStxAux___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_formatStxAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_formatStxAux(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instToFormat___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instToStringTSyntax___boxed(lean_object*);
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_formatStx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instToFormatTSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instToStringTSyntax___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Syntax_formatStxAux_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_formatStxAux___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instToString;
LEAN_EXPORT lean_object* l_Lean_Syntax_instToFormatTSyntax___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instToString___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_formatStxAux___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Syntax_formatStxAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instToFormatTSyntax___lam__0(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instToStringTSyntax(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instToFormat;
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (x_1 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 2);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_mk_string_unchecked("", 0, 0);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_string_utf8_extract(x_8, x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_14 = l_String_quote(x_13);
lean_dec(x_13);
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_inc(x_12);
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_mk_string_unchecked(":", 1, 1);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_inc(x_18);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l___private_Init_Data_Repr_0__Nat_reprFast(x_5);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
lean_inc(x_18);
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_3);
x_25 = l___private_Init_Data_Repr_0__Nat_reprFast(x_7);
x_26 = lean_ctor_get(x_6, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_6, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_6, 2);
lean_inc(x_28);
lean_dec(x_6);
lean_inc(x_18);
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_18);
x_30 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_30, 0, x_25);
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_18);
x_33 = lean_string_utf8_extract(x_26, x_27, x_28);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
x_34 = l_String_quote(x_33);
lean_dec(x_33);
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_12);
return x_37;
}
case 1:
{
uint8_t x_38; 
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_39 = lean_ctor_get(x_2, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_2, 1);
lean_inc(x_40);
lean_dec(x_2);
x_41 = lean_mk_string_unchecked("", 0, 0);
x_42 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = l___private_Init_Data_Repr_0__Nat_reprFast(x_39);
x_44 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_44, 0, x_43);
lean_inc(x_42);
x_45 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_mk_string_unchecked(":", 1, 1);
x_47 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_47, 0, x_46);
lean_inc(x_47);
x_48 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_3);
x_50 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
x_51 = l___private_Init_Data_Repr_0__Nat_reprFast(x_40);
x_52 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_42);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_55 = lean_ctor_get(x_2, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_2, 1);
lean_inc(x_56);
lean_dec(x_2);
x_57 = lean_mk_string_unchecked("", 0, 0);
x_58 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = l___private_Init_Data_Repr_0__Nat_reprFast(x_55);
x_60 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_60, 0, x_59);
lean_inc(x_58);
x_61 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_mk_string_unchecked("!:", 2, 2);
x_63 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_3);
x_66 = lean_mk_string_unchecked(":", 1, 1);
x_67 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_68 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_67);
x_69 = l___private_Init_Data_Repr_0__Nat_reprFast(x_56);
x_70 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_58);
return x_72;
}
}
default: 
{
return x_3;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Syntax_formatStxAux_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = l_List_reverse___redArg(x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_inc(x_1);
x_12 = l_Lean_Syntax_formatStxAux(x_1, x_2, x_11, x_8);
lean_dec(x_11);
lean_ctor_set(x_4, 1, x_5);
lean_ctor_set(x_4, 0, x_12);
{
lean_object* _tmp_3 = x_9;
lean_object* _tmp_4 = x_4;
x_4 = _tmp_3;
x_5 = _tmp_4;
}
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_4);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_3, x_16);
lean_inc(x_1);
x_18 = l_Lean_Syntax_formatStxAux(x_1, x_2, x_17, x_14);
lean_dec(x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_5);
x_4 = x_15;
x_5 = x_19;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 0, x_2);
x_7 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
x_2 = x_7;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
lean_inc(x_1);
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_1);
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
x_2 = x_12;
x_3 = x_10;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_List_foldl___at___Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1_spec__1(x_2, x_6, x_4);
return x_7;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_formatStxAux___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_formatStxAux___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_formatStxAux(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_19 = lean_mk_string_unchecked("<missing>", 9, 9);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
case 1:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_4, 2);
lean_inc(x_23);
lean_dec(x_4);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_3, x_33);
x_38 = lean_mk_string_unchecked("null", 4, 4);
x_39 = l_Lean_Name_mkStr1(x_38);
x_40 = lean_name_eq(x_22, x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_69; lean_object* x_78; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_41 = lean_box(x_40);
x_42 = lean_alloc_closure((void*)(l_Lean_Syntax_formatStxAux___lam__0___boxed), 2, 1);
lean_closure_set(x_42, 0, x_41);
x_43 = lean_mk_string_unchecked("Lean", 4, 4);
x_44 = lean_mk_string_unchecked("Parser", 6, 6);
x_45 = l_Lean_Name_mkStr2(x_43, x_44);
x_46 = lean_box(0);
x_47 = l_Lean_Name_replacePrefix(x_22, x_45, x_46);
lean_dec(x_45);
x_48 = lean_box(1);
x_49 = lean_unbox(x_48);
x_50 = l_Lean_Name_toString(x_47, x_49, x_42);
x_51 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo(x_2, x_21, x_51);
x_81 = lean_unsigned_to_nat(0u);
x_82 = lean_array_get_size(x_23);
x_83 = lean_nat_dec_lt(x_81, x_82);
lean_dec(x_82);
if (x_83 == 0)
{
lean_dec(x_34);
x_69 = x_83;
goto block_77;
}
else
{
if (lean_obj_tag(x_1) == 0)
{
lean_inc(x_34);
x_78 = x_34;
goto block_80;
}
else
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_1, 0);
lean_inc(x_84);
x_78 = x_84;
goto block_80;
}
}
block_68:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_box(1);
x_56 = l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(x_54, x_55);
x_57 = lean_mk_string_unchecked("(", 1, 1);
x_58 = lean_mk_string_unchecked(")", 1, 1);
x_59 = lean_nat_to_int(x_33);
x_60 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_60, 0, x_57);
x_61 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_56);
x_62 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_62, 0, x_58);
x_63 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_64, 0, x_59);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_66, 0, x_64);
x_67 = lean_unbox(x_65);
lean_ctor_set_uint8(x_66, sizeof(void*)*1, x_67);
return x_66;
}
block_77:
{
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_array_to_list(x_23);
x_71 = lean_box(0);
x_72 = l_List_mapTR_loop___at___Lean_Syntax_formatStxAux_spec__0(x_1, x_2, x_3, x_70, x_71);
x_53 = x_72;
goto block_68;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_23);
lean_dec(x_1);
x_73 = lean_mk_string_unchecked("..", 2, 2);
x_74 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_53 = x_76;
goto block_68;
}
}
block_80:
{
uint8_t x_79; 
x_79 = lean_nat_dec_lt(x_78, x_34);
lean_dec(x_34);
lean_dec(x_78);
x_69 = x_79;
goto block_77;
}
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
lean_dec(x_22);
lean_dec(x_21);
x_85 = lean_unsigned_to_nat(0u);
x_86 = lean_array_get_size(x_23);
x_87 = lean_nat_dec_lt(x_85, x_86);
lean_dec(x_86);
if (x_87 == 0)
{
lean_dec(x_34);
x_24 = x_87;
goto block_32;
}
else
{
if (lean_obj_tag(x_1) == 0)
{
lean_inc(x_34);
x_35 = x_34;
goto block_37;
}
else
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_1, 0);
lean_inc(x_88);
x_35 = x_88;
goto block_37;
}
}
}
block_32:
{
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_array_to_list(x_23);
x_26 = lean_box(0);
x_27 = l_List_mapTR_loop___at___Lean_Syntax_formatStxAux_spec__0(x_1, x_2, x_3, x_25, x_26);
x_28 = lean_box(1);
x_29 = l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(x_27, x_28);
x_5 = x_29;
goto block_18;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_23);
lean_dec(x_1);
x_30 = lean_mk_string_unchecked("..", 2, 2);
x_31 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_5 = x_31;
goto block_18;
}
}
block_37:
{
uint8_t x_36; 
x_36 = lean_nat_dec_lt(x_35, x_34);
lean_dec(x_34);
lean_dec(x_35);
x_24 = x_36;
goto block_32;
}
}
case 2:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_1);
x_89 = lean_ctor_get(x_4, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_4, 1);
lean_inc(x_90);
lean_dec(x_4);
x_91 = l_String_quote(x_90);
lean_dec(x_90);
x_92 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_93 = l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo(x_2, x_89, x_92);
return x_93;
}
default: 
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_1);
x_94 = lean_ctor_get(x_4, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_4, 2);
lean_inc(x_95);
lean_dec(x_4);
x_96 = lean_alloc_closure((void*)(l_Lean_Syntax_formatStxAux___lam__1___boxed), 1, 0);
x_97 = lean_mk_string_unchecked("`", 1, 1);
x_98 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = lean_box(1);
x_100 = lean_unbox(x_99);
x_101 = l_Lean_Name_toString(x_95, x_100, x_96);
x_102 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_103 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_103, 0, x_98);
lean_ctor_set(x_103, 1, x_102);
x_104 = l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo(x_2, x_94, x_103);
return x_104;
}
}
block_18:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_6 = lean_mk_string_unchecked("[", 1, 1);
x_7 = lean_mk_string_unchecked("]", 1, 1);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_to_int(x_8);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_6);
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_7);
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_unbox(x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_17);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Syntax_formatStxAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_List_mapTR_loop___at___Lean_Syntax_formatStxAux_spec__0(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_formatStxAux___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Syntax_formatStxAux___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_formatStxAux___lam__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Syntax_formatStxAux___lam__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_formatStxAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Syntax_formatStxAux(x_1, x_5, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_formatStx(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Syntax_formatStxAux(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_formatStx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Syntax_formatStx(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instToFormat___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
x_5 = l_Lean_Syntax_formatStx(x_1, x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Syntax_instToFormat() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Syntax_instToFormat___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instToString___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(120u);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_format_pretty(x_1, x_2, x_3, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Syntax_instToString() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_Syntax_instToString___lam__0), 1, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_instToFormat___lam__0), 1, 0);
x_3 = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, lean_box(0));
lean_closure_set(x_3, 2, lean_box(0));
lean_closure_set(x_3, 3, x_1);
lean_closure_set(x_3, 4, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instToFormatTSyntax___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
x_5 = l_Lean_Syntax_formatStx(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instToFormatTSyntax(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_instToFormatTSyntax___lam__0), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instToFormatTSyntax___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_instToFormatTSyntax(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instToStringTSyntax___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
x_5 = l_Lean_Syntax_formatStx(x_1, x_2, x_4);
x_6 = lean_unsigned_to_nat(120u);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_format_pretty(x_5, x_6, x_7, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instToStringTSyntax(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_instToStringTSyntax___lam__0), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instToStringTSyntax___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_instToStringTSyntax(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init_Data_Format_Macro(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Format_Instances(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Meta(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Format_Syntax(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Format_Macro(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Format_Instances(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Meta(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Syntax_instToFormat = _init_l_Lean_Syntax_instToFormat();
lean_mark_persistent(l_Lean_Syntax_instToFormat);
l_Lean_Syntax_instToString = _init_l_Lean_Syntax_instToString();
lean_mark_persistent(l_Lean_Syntax_instToString);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
