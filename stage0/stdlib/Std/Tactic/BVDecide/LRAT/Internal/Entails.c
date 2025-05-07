// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Entails
// Imports: Init.NotationExtra Init.PropLemmas
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______unexpand__Std__Tactic__BVDecide__LRAT__Internal__Entails__eval__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad__;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8__;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______unexpand__Std__Tactic__BVDecide__LRAT__Internal__Entails__eval__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8__() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_1 = lean_mk_string_unchecked("Std", 3, 3);
x_2 = lean_mk_string_unchecked("Tactic", 6, 6);
x_3 = lean_mk_string_unchecked("BVDecide", 8, 8);
x_4 = lean_mk_string_unchecked("LRAT", 4, 4);
x_5 = lean_mk_string_unchecked("Internal", 8, 8);
x_6 = lean_mk_string_unchecked("term_⊨_", 9, 7);
x_7 = l_Lean_Name_mkStr6(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = lean_unsigned_to_nat(25u);
x_9 = lean_unsigned_to_nat(26u);
x_10 = lean_mk_string_unchecked("andthen", 7, 7);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_mk_string_unchecked(" ⊨ ", 5, 3);
x_13 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_mk_string_unchecked("term", 4, 4);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_9);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_8);
lean_ctor_set(x_18, 2, x_9);
lean_ctor_set(x_18, 3, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_mk_string_unchecked("Std", 3, 3);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("BVDecide", 8, 8);
x_7 = lean_mk_string_unchecked("LRAT", 4, 4);
x_8 = lean_mk_string_unchecked("Internal", 8, 8);
x_9 = lean_mk_string_unchecked("term_⊨_", 9, 7);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_10 = l_Lean_Name_mkStr6(x_4, x_5, x_6, x_7, x_8, x_9);
lean_inc(x_1);
x_11 = l_Lean_Syntax_isOfKind(x_1, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = lean_unsigned_to_nat(2u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
lean_dec(x_1);
x_18 = lean_ctor_get(x_2, 5);
lean_inc(x_18);
x_19 = lean_box(0);
x_20 = lean_unbox(x_19);
x_21 = l_Lean_SourceInfo_fromRef(x_18, x_20);
lean_dec(x_18);
x_22 = lean_ctor_get(x_2, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_dec(x_2);
x_24 = lean_mk_string_unchecked("Lean", 4, 4);
x_25 = lean_mk_string_unchecked("Parser", 6, 6);
x_26 = lean_mk_string_unchecked("Term", 4, 4);
x_27 = lean_mk_string_unchecked("app", 3, 3);
x_28 = l_Lean_Name_mkStr4(x_24, x_25, x_26, x_27);
x_29 = lean_mk_string_unchecked("Entails.eval", 12, 12);
x_30 = l_String_toSubstring_x27(x_29);
x_31 = lean_mk_string_unchecked("Entails", 7, 7);
x_32 = lean_mk_string_unchecked("eval", 4, 4);
lean_inc(x_32);
lean_inc(x_31);
x_33 = l_Lean_Name_mkStr2(x_31, x_32);
x_34 = l_Lean_addMacroScope(x_23, x_33, x_22);
x_35 = l_Lean_Name_mkStr7(x_4, x_5, x_6, x_7, x_8, x_31, x_32);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
lean_inc(x_21);
x_40 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_40, 0, x_21);
lean_ctor_set(x_40, 1, x_30);
lean_ctor_set(x_40, 2, x_34);
lean_ctor_set(x_40, 3, x_39);
x_41 = lean_mk_string_unchecked("null", 4, 4);
x_42 = l_Lean_Name_mkStr1(x_41);
lean_inc(x_21);
x_43 = l_Lean_Syntax_node2(x_21, x_42, x_15, x_17);
x_44 = l_Lean_Syntax_node2(x_21, x_28, x_40, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_3);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______unexpand__Std__Tactic__BVDecide__LRAT__Internal__Entails__eval__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("app", 3, 3);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
lean_inc(x_1);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = lean_mk_string_unchecked("ident", 5, 5);
x_15 = l_Lean_Name_mkStr1(x_14);
lean_inc(x_13);
x_16 = l_Lean_Syntax_isOfKind(x_13, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_3);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
lean_dec(x_1);
x_21 = lean_unsigned_to_nat(2u);
lean_inc(x_20);
x_22 = l_Lean_Syntax_matchesNull(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_20);
lean_dec(x_13);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_3);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_25 = l_Lean_Syntax_getArg(x_20, x_12);
x_26 = l_Lean_Syntax_getArg(x_20, x_19);
lean_dec(x_20);
x_27 = l_Lean_replaceRef(x_13, x_2);
lean_dec(x_13);
x_28 = lean_box(0);
x_29 = lean_unbox(x_28);
x_30 = l_Lean_SourceInfo_fromRef(x_27, x_29);
lean_dec(x_27);
x_31 = lean_mk_string_unchecked("Std", 3, 3);
x_32 = lean_mk_string_unchecked("Tactic", 6, 6);
x_33 = lean_mk_string_unchecked("BVDecide", 8, 8);
x_34 = lean_mk_string_unchecked("LRAT", 4, 4);
x_35 = lean_mk_string_unchecked("Internal", 8, 8);
x_36 = lean_mk_string_unchecked("term_⊨_", 9, 7);
x_37 = l_Lean_Name_mkStr6(x_31, x_32, x_33, x_34, x_35, x_36);
x_38 = lean_mk_string_unchecked(" ⊨ ", 5, 3);
lean_inc(x_30);
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_30);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Syntax_node3(x_30, x_37, x_25, x_39, x_26);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_3);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______unexpand__Std__Tactic__BVDecide__LRAT__Internal__Entails__eval__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______unexpand__Std__Tactic__BVDecide__LRAT__Internal__Entails__eval__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad__() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_1 = lean_mk_string_unchecked("Std", 3, 3);
x_2 = lean_mk_string_unchecked("Tactic", 6, 6);
x_3 = lean_mk_string_unchecked("BVDecide", 8, 8);
x_4 = lean_mk_string_unchecked("LRAT", 4, 4);
x_5 = lean_mk_string_unchecked("Internal", 8, 8);
x_6 = lean_mk_string_unchecked("term_⊭_", 9, 7);
x_7 = l_Lean_Name_mkStr6(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = lean_unsigned_to_nat(25u);
x_9 = lean_mk_string_unchecked("andthen", 7, 7);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_mk_string_unchecked(" ⊭ ", 5, 3);
x_12 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_mk_string_unchecked("term", 4, 4);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_unsigned_to_nat(30u);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_12);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_8);
lean_ctor_set(x_18, 2, x_8);
lean_ctor_set(x_18, 3, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_mk_string_unchecked("Std", 3, 3);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("BVDecide", 8, 8);
x_7 = lean_mk_string_unchecked("LRAT", 4, 4);
x_8 = lean_mk_string_unchecked("Internal", 8, 8);
x_9 = lean_mk_string_unchecked("term_⊭_", 9, 7);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_10 = l_Lean_Name_mkStr6(x_4, x_5, x_6, x_7, x_8, x_9);
lean_inc(x_1);
x_11 = l_Lean_Syntax_isOfKind(x_1, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = lean_unsigned_to_nat(2u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
lean_dec(x_1);
x_18 = lean_ctor_get(x_2, 5);
lean_inc(x_18);
x_19 = lean_box(0);
x_20 = lean_unbox(x_19);
x_21 = l_Lean_SourceInfo_fromRef(x_18, x_20);
lean_dec(x_18);
x_22 = lean_ctor_get(x_2, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_dec(x_2);
x_24 = lean_mk_string_unchecked("term¬_", 7, 6);
x_25 = l_Lean_Name_mkStr1(x_24);
x_26 = lean_mk_string_unchecked("¬", 2, 1);
lean_inc(x_21);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_mk_string_unchecked("Lean", 4, 4);
x_29 = lean_mk_string_unchecked("Parser", 6, 6);
x_30 = lean_mk_string_unchecked("Term", 4, 4);
x_31 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
x_32 = l_Lean_Name_mkStr4(x_28, x_29, x_30, x_31);
x_33 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_21);
x_34 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_34, 0, x_21);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_mk_string_unchecked("app", 3, 3);
x_36 = l_Lean_Name_mkStr4(x_28, x_29, x_30, x_35);
x_37 = lean_mk_string_unchecked("Entails.eval", 12, 12);
x_38 = l_String_toSubstring_x27(x_37);
x_39 = lean_mk_string_unchecked("Entails", 7, 7);
x_40 = lean_mk_string_unchecked("eval", 4, 4);
lean_inc(x_40);
lean_inc(x_39);
x_41 = l_Lean_Name_mkStr2(x_39, x_40);
x_42 = l_Lean_addMacroScope(x_23, x_41, x_22);
x_43 = l_Lean_Name_mkStr7(x_4, x_5, x_6, x_7, x_8, x_39, x_40);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
lean_inc(x_21);
x_48 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_48, 0, x_21);
lean_ctor_set(x_48, 1, x_38);
lean_ctor_set(x_48, 2, x_42);
lean_ctor_set(x_48, 3, x_47);
x_49 = lean_mk_string_unchecked("null", 4, 4);
x_50 = l_Lean_Name_mkStr1(x_49);
lean_inc(x_21);
x_51 = l_Lean_Syntax_node2(x_21, x_50, x_15, x_17);
lean_inc(x_21);
x_52 = l_Lean_Syntax_node2(x_21, x_36, x_48, x_51);
x_53 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_21);
x_54 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_54, 0, x_21);
lean_ctor_set(x_54, 1, x_53);
lean_inc(x_21);
x_55 = l_Lean_Syntax_node3(x_21, x_32, x_34, x_52, x_54);
x_56 = l_Lean_Syntax_node2(x_21, x_25, x_27, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_3);
return x_57;
}
}
}
lean_object* initialize_Init_NotationExtra(uint8_t builtin, lean_object*);
lean_object* initialize_Init_PropLemmas(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Entails(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_NotationExtra(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_PropLemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8__ = _init_l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8__();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8__);
l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad__ = _init_l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad__();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad__);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
