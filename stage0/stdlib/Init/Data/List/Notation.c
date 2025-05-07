// Lean compiler output
// Module: Init.Data.List.Notation
// Imports: Init.Data.Nat.Div.Basic
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
LEAN_EXPORT lean_object* l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_term_x5b___x5d;
LEAN_EXPORT lean_object* l_term_x25_x5b___x7c___x5d;
lean_object* l_Array_appendCore___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSyntax;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
static lean_object* _init_l_term_x5b___x5d() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_1 = lean_mk_string_unchecked("term[_]", 7, 7);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_unsigned_to_nat(1024u);
x_4 = lean_mk_string_unchecked("andthen", 7, 7);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_mk_string_unchecked("[", 1, 1);
x_7 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_mk_string_unchecked("withoutPosition", 15, 15);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("term", 4, 4);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_mk_string_unchecked(",", 1, 1);
x_15 = lean_mk_string_unchecked(", ", 2, 2);
x_16 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_box(1);
x_18 = lean_alloc_ctor(10, 3, 1);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_16);
x_19 = lean_unbox(x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_19);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_18);
lean_inc(x_5);
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_7);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_mk_string_unchecked("]", 1, 1);
x_23 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_24, 0, x_5);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_3);
lean_ctor_set(x_25, 2, x_24);
return x_25;
}
}
static lean_object* _init_l_term_x25_x5b___x7c___x5d() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_1 = lean_mk_string_unchecked("term%[_|_]", 10, 10);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_unsigned_to_nat(1024u);
x_4 = lean_mk_string_unchecked("andthen", 7, 7);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_mk_string_unchecked("%[", 2, 2);
x_7 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_mk_string_unchecked("withoutPosition", 15, 15);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("term", 4, 4);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_mk_string_unchecked(",", 1, 1);
x_15 = lean_mk_string_unchecked(", ", 2, 2);
x_16 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_box(1);
lean_inc(x_13);
x_18 = lean_alloc_ctor(10, 3, 1);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_16);
x_19 = lean_unbox(x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_19);
x_20 = lean_mk_string_unchecked(" | ", 3, 3);
x_21 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_inc(x_5);
x_22 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_21);
lean_inc(x_5);
x_23 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_13);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_9);
lean_ctor_set(x_24, 1, x_23);
lean_inc(x_5);
x_25 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_7);
lean_ctor_set(x_25, 2, x_24);
x_26 = lean_mk_string_unchecked("]", 1, 1);
x_27 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_25);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 2, x_28);
return x_29;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_2, x_7);
if (x_8 == 1)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_2, x_10);
lean_dec(x_2);
if (x_3 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_12 = l_Lean_instInhabitedSyntax;
x_13 = lean_ctor_get(x_5, 5);
lean_inc(x_13);
x_14 = l_Lean_SourceInfo_fromRef(x_13, x_3);
lean_dec(x_13);
x_15 = lean_ctor_get(x_5, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
x_17 = lean_mk_string_unchecked("Lean", 4, 4);
x_18 = lean_mk_string_unchecked("Parser", 6, 6);
x_19 = lean_mk_string_unchecked("Term", 4, 4);
x_20 = lean_mk_string_unchecked("app", 3, 3);
x_21 = l_Lean_Name_mkStr4(x_17, x_18, x_19, x_20);
x_22 = lean_mk_string_unchecked("List.cons", 9, 9);
x_23 = l_String_toSubstring_x27(x_22);
x_24 = lean_mk_string_unchecked("List", 4, 4);
x_25 = lean_mk_string_unchecked("cons", 4, 4);
x_26 = l_Lean_Name_mkStr2(x_24, x_25);
lean_inc(x_26);
x_27 = l_Lean_addMacroScope(x_16, x_26, x_15);
x_28 = lean_box(0);
lean_inc(x_26);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_26);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_32);
lean_inc(x_14);
x_34 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_34, 0, x_14);
lean_ctor_set(x_34, 1, x_23);
lean_ctor_set(x_34, 2, x_27);
lean_ctor_set(x_34, 3, x_33);
x_35 = lean_mk_string_unchecked("null", 4, 4);
x_36 = l_Lean_Name_mkStr1(x_35);
x_37 = lean_array_get(x_12, x_1, x_11);
lean_inc(x_14);
x_38 = l_Lean_Syntax_node2(x_14, x_36, x_37, x_4);
x_39 = l_Lean_Syntax_node2(x_14, x_21, x_34, x_38);
x_40 = lean_box(1);
x_41 = lean_unbox(x_40);
x_2 = x_11;
x_3 = x_41;
x_4 = x_39;
goto _start;
}
else
{
x_2 = x_11;
x_3 = x_8;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_mk_string_unchecked("term[_]", 7, 7);
x_5 = l_Lean_Name_mkStr1(x_4);
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(1);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
lean_dec(x_1);
x_11 = l_Lean_Syntax_getArgs(x_10);
lean_dec(x_10);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(64u);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_12);
x_15 = lean_ctor_get(x_2, 5);
lean_inc(x_15);
x_16 = l_Lean_SourceInfo_fromRef(x_15, x_14);
lean_dec(x_15);
x_17 = lean_ctor_get(x_2, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_mk_string_unchecked("term%[_|_]", 10, 10);
x_20 = l_Lean_Name_mkStr1(x_19);
x_21 = lean_mk_string_unchecked("%[", 2, 2);
lean_inc(x_16);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_mk_string_unchecked("null", 4, 4);
x_24 = l_Lean_Name_mkStr1(x_23);
x_25 = l_Array_mkArray0(lean_box(0));
x_26 = l_Array_appendCore___redArg(x_25, x_11);
lean_dec(x_11);
lean_inc(x_16);
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_26);
x_28 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_16);
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_16);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_mk_string_unchecked("List.nil", 8, 8);
x_31 = l_String_toSubstring_x27(x_30);
x_32 = lean_mk_string_unchecked("List", 4, 4);
x_33 = lean_mk_string_unchecked("nil", 3, 3);
x_34 = l_Lean_Name_mkStr2(x_32, x_33);
lean_inc(x_34);
x_35 = l_Lean_addMacroScope(x_18, x_34, x_17);
x_36 = lean_box(0);
lean_inc(x_34);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_34);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
lean_inc(x_16);
x_42 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_42, 0, x_16);
lean_ctor_set(x_42, 1, x_31);
lean_ctor_set(x_42, 2, x_35);
lean_ctor_set(x_42, 3, x_41);
x_43 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_16);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_16);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_Syntax_node5(x_16, x_20, x_22, x_27, x_29, x_42, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_3);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; 
x_47 = lean_unsigned_to_nat(0u);
x_48 = lean_unsigned_to_nat(2u);
x_49 = lean_ctor_get(x_2, 5);
lean_inc(x_49);
x_50 = lean_box(0);
x_51 = lean_unbox(x_50);
x_52 = l_Lean_SourceInfo_fromRef(x_49, x_51);
lean_dec(x_49);
x_53 = lean_ctor_get(x_2, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_2, 1);
lean_inc(x_54);
x_55 = lean_mk_string_unchecked("List.nil", 8, 8);
x_56 = l_String_toSubstring_x27(x_55);
x_57 = lean_mk_string_unchecked("List", 4, 4);
x_58 = lean_mk_string_unchecked("nil", 3, 3);
x_59 = l_Lean_Name_mkStr2(x_57, x_58);
lean_inc(x_59);
x_60 = l_Lean_addMacroScope(x_54, x_59, x_53);
x_61 = lean_box(0);
lean_inc(x_59);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_59);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_62);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_67, 0, x_52);
lean_ctor_set(x_67, 1, x_56);
lean_ctor_set(x_67, 2, x_60);
lean_ctor_set(x_67, 3, x_66);
x_68 = lean_nat_mod(x_12, x_48);
x_69 = lean_nat_dec_eq(x_68, x_47);
lean_dec(x_68);
x_70 = l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit(x_11, x_12, x_69, x_67, x_2, x_3);
lean_dec(x_11);
return x_70;
}
}
}
}
lean_object* initialize_Init_Data_Nat_Div_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_Notation(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Div_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_term_x5b___x5d = _init_l_term_x5b___x5d();
lean_mark_persistent(l_term_x5b___x5d);
l_term_x25_x5b___x7c___x5d = _init_l_term_x25_x5b___x7c___x5d();
lean_mark_persistent(l_term_x25_x5b___x7c___x5d);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
