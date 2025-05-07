// Lean compiler output
// Module: Init.Grind.Tactics
// Imports: Init.Tactics
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
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_grindUsr;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_grindBwd;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_grindFwd;
extern lean_object* l_Lean_Parser_Tactic_optConfig;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_grindEqBwd;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_grindEqRhs;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_grindCasesEager;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_grindParam;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_grind;
LEAN_EXPORT lean_object* l___private_Init_Grind_Tactics_0__Lean_Grind_beqConfig____x40_Init_Grind_Tactics___hyg_410____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_grind;
LEAN_EXPORT lean_object* l_Lean_Grind_instBEqConfig;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_grindTrace;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_grindMod;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_grindErase;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_grindEqBoth;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_grindLemma;
LEAN_EXPORT lean_object* l_Lean_Grind_instInhabitedConfig;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_grindIntro;
LEAN_EXPORT uint8_t l___private_Init_Grind_Tactics_0__Lean_Grind_beqConfig____x40_Init_Grind_Tactics___hyg_410_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_resetGrindAttrs;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_grindCases;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_grindLR;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_grindEq;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_grindRL;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_grindExt;
static lean_object* _init_l_Lean_Parser_resetGrindAttrs() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("resetGrindAttrs", 15, 15);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
x_5 = lean_unsigned_to_nat(1024u);
x_6 = lean_mk_string_unchecked("reset_grind_attrs%", 18, 18);
x_7 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEq() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = lean_mk_string_unchecked("grindEq", 7, 7);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Attr", 4, 4);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("= ", 2, 2);
x_7 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqBoth() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_1 = lean_mk_string_unchecked("grindEqBoth", 11, 11);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Attr", 4, 4);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("atomic", 6, 6);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("andthen", 7, 7);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("_", 1, 1);
x_11 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_mk_string_unchecked("=", 1, 1);
x_13 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_inc(x_9);
x_14 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_mk_string_unchecked("_ ", 2, 2);
x_16 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_14);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_5);
lean_ctor_set(x_19, 2, x_18);
return x_19;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqRhs() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_1 = lean_mk_string_unchecked("grindEqRhs", 10, 10);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Attr", 4, 4);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("atomic", 6, 6);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("andthen", 7, 7);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("=", 1, 1);
x_11 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_mk_string_unchecked("_ ", 2, 2);
x_13 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_5);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindEqBwd() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_1 = lean_mk_string_unchecked("grindEqBwd", 10, 10);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Attr", 4, 4);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("orelse", 6, 6);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("group", 5, 5);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("atomic", 6, 6);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_mk_string_unchecked("andthen", 7, 7);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_mk_string_unchecked("←", 3, 1);
x_15 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_mk_string_unchecked("= ", 2, 2);
x_17 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_inc(x_17);
lean_inc(x_13);
x_18 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_17);
lean_inc(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_18);
lean_inc(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_mk_string_unchecked("<-", 2, 2);
x_22 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_23, 0, x_13);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_17);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_20);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_5);
lean_ctor_set(x_27, 2, x_26);
return x_27;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindBwd() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_1 = lean_mk_string_unchecked("grindBwd", 8, 8);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Attr", 4, 4);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("orelse", 6, 6);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("← ", 4, 2);
x_9 = lean_mk_string_unchecked("token", 5, 5);
lean_inc(x_8);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr2(x_9, x_8);
lean_inc(x_8);
x_11 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_11, 0, x_8);
x_12 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
x_13 = lean_mk_string_unchecked("-> ", 3, 3);
lean_inc(x_13);
x_14 = l_Lean_Name_mkStr2(x_9, x_13);
lean_inc(x_13);
x_15 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_12);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_5);
lean_ctor_set(x_18, 2, x_17);
return x_18;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindFwd() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_1 = lean_mk_string_unchecked("grindFwd", 8, 8);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Attr", 4, 4);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("orelse", 6, 6);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("→ ", 4, 2);
x_9 = lean_mk_string_unchecked("token", 5, 5);
lean_inc(x_8);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr2(x_9, x_8);
lean_inc(x_8);
x_11 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_11, 0, x_8);
x_12 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
x_13 = lean_mk_string_unchecked("<- ", 3, 3);
lean_inc(x_13);
x_14 = l_Lean_Name_mkStr2(x_9, x_13);
lean_inc(x_13);
x_15 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_12);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_5);
lean_ctor_set(x_18, 2, x_17);
return x_18;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindRL() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_1 = lean_mk_string_unchecked("grindRL", 7, 7);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Attr", 4, 4);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("orelse", 6, 6);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("⇐ ", 4, 2);
x_9 = lean_mk_string_unchecked("token", 5, 5);
lean_inc(x_8);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr2(x_9, x_8);
lean_inc(x_8);
x_11 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_11, 0, x_8);
x_12 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
x_13 = lean_mk_string_unchecked("<= ", 3, 3);
lean_inc(x_13);
x_14 = l_Lean_Name_mkStr2(x_9, x_13);
lean_inc(x_13);
x_15 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_12);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_5);
lean_ctor_set(x_18, 2, x_17);
return x_18;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindLR() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_1 = lean_mk_string_unchecked("grindLR", 7, 7);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Attr", 4, 4);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("orelse", 6, 6);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("⇒ ", 4, 2);
x_9 = lean_mk_string_unchecked("token", 5, 5);
lean_inc(x_8);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr2(x_9, x_8);
lean_inc(x_8);
x_11 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_11, 0, x_8);
x_12 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
x_13 = lean_mk_string_unchecked("=> ", 3, 3);
lean_inc(x_13);
x_14 = l_Lean_Name_mkStr2(x_9, x_13);
lean_inc(x_13);
x_15 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_12);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_5);
lean_ctor_set(x_18, 2, x_17);
return x_18;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindUsr() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_1 = lean_mk_string_unchecked("grindUsr", 8, 8);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Attr", 4, 4);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("usr ", 4, 4);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_9);
x_10 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindCases() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_1 = lean_mk_string_unchecked("grindCases", 10, 10);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Attr", 4, 4);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("cases ", 6, 6);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_9);
x_10 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindCasesEager() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_1 = lean_mk_string_unchecked("grindCasesEager", 15, 15);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Attr", 4, 4);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("atomic", 6, 6);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("andthen", 7, 7);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("cases", 5, 5);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_12, 0, x_10);
x_13 = lean_unbox(x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_13);
x_14 = lean_mk_string_unchecked("eager ", 6, 6);
x_15 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_unbox(x_11);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_16);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_12);
lean_ctor_set(x_17, 2, x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_5);
lean_ctor_set(x_19, 2, x_18);
return x_19;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindIntro() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_1 = lean_mk_string_unchecked("grindIntro", 10, 10);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Attr", 4, 4);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("intro ", 6, 6);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_9);
x_10 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindExt() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_1 = lean_mk_string_unchecked("grindExt", 8, 8);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Attr", 4, 4);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("ext ", 4, 4);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_9);
x_10 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grindMod() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_1 = lean_mk_string_unchecked("grindMod", 8, 8);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Attr", 4, 4);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("orelse", 6, 6);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = l_Lean_Parser_Attr_grindEqBoth;
x_9 = l_Lean_Parser_Attr_grindEqRhs;
x_10 = l_Lean_Parser_Attr_grindEq;
x_11 = l_Lean_Parser_Attr_grindEqBwd;
x_12 = l_Lean_Parser_Attr_grindBwd;
x_13 = l_Lean_Parser_Attr_grindFwd;
x_14 = l_Lean_Parser_Attr_grindRL;
x_15 = l_Lean_Parser_Attr_grindLR;
x_16 = l_Lean_Parser_Attr_grindUsr;
x_17 = l_Lean_Parser_Attr_grindCasesEager;
x_18 = l_Lean_Parser_Attr_grindCases;
x_19 = l_Lean_Parser_Attr_grindIntro;
x_20 = l_Lean_Parser_Attr_grindExt;
lean_inc(x_7);
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_20);
lean_inc(x_7);
x_22 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_22, 0, x_7);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_21);
lean_inc(x_7);
x_23 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_23, 0, x_7);
lean_ctor_set(x_23, 1, x_17);
lean_ctor_set(x_23, 2, x_22);
lean_inc(x_7);
x_24 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_24, 0, x_7);
lean_ctor_set(x_24, 1, x_16);
lean_ctor_set(x_24, 2, x_23);
lean_inc(x_7);
x_25 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_25, 0, x_7);
lean_ctor_set(x_25, 1, x_15);
lean_ctor_set(x_25, 2, x_24);
lean_inc(x_7);
x_26 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_14);
lean_ctor_set(x_26, 2, x_25);
lean_inc(x_7);
x_27 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_27, 0, x_7);
lean_ctor_set(x_27, 1, x_13);
lean_ctor_set(x_27, 2, x_26);
lean_inc(x_7);
x_28 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_28, 0, x_7);
lean_ctor_set(x_28, 1, x_12);
lean_ctor_set(x_28, 2, x_27);
lean_inc(x_7);
x_29 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_29, 0, x_7);
lean_ctor_set(x_29, 1, x_11);
lean_ctor_set(x_29, 2, x_28);
lean_inc(x_7);
x_30 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_30, 0, x_7);
lean_ctor_set(x_30, 1, x_10);
lean_ctor_set(x_30, 2, x_29);
lean_inc(x_7);
x_31 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_31, 0, x_7);
lean_ctor_set(x_31, 1, x_9);
lean_ctor_set(x_31, 2, x_30);
x_32 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_32, 0, x_7);
lean_ctor_set(x_32, 1, x_8);
lean_ctor_set(x_32, 2, x_31);
x_33 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_5);
lean_ctor_set(x_33, 2, x_32);
return x_33;
}
}
static lean_object* _init_l_Lean_Parser_Attr_grind() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Attr", 4, 4);
x_4 = lean_mk_string_unchecked("grind", 5, 5);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_11);
x_12 = lean_mk_string_unchecked("optional", 8, 8);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = l_Lean_Parser_Attr_grindMod;
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_16);
return x_17;
}
}
static lean_object* _init_l_Lean_Grind_instInhabitedConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 7, 18);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_2);
lean_ctor_set(x_3, 5, x_2);
lean_ctor_set(x_3, 6, x_2);
x_4 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*7, x_4);
x_5 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*7 + 1, x_5);
x_6 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*7 + 2, x_6);
x_7 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*7 + 3, x_7);
x_8 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*7 + 4, x_8);
x_9 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*7 + 5, x_9);
x_10 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*7 + 6, x_10);
x_11 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*7 + 7, x_11);
x_12 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*7 + 8, x_12);
x_13 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*7 + 9, x_13);
x_14 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*7 + 10, x_14);
x_15 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*7 + 11, x_15);
x_16 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*7 + 12, x_16);
x_17 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*7 + 13, x_17);
x_18 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*7 + 14, x_18);
x_19 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*7 + 15, x_19);
x_20 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*7 + 16, x_20);
x_21 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*7 + 17, x_21);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Init_Grind_Tactics_0__Lean_Grind_beqConfig____x40_Init_Grind_Tactics___hyg_410_(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; lean_object* x_51; uint8_t x_52; uint8_t x_91; uint8_t x_114; lean_object* x_127; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 1);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 2);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 3);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 4);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 5);
x_13 = lean_ctor_get(x_1, 4);
x_14 = lean_ctor_get(x_1, 5);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 6);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 7);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 8);
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 9);
x_19 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 10);
x_20 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 11);
x_21 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 12);
x_22 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 13);
x_23 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 14);
x_24 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 15);
x_25 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 16);
x_26 = lean_ctor_get(x_1, 6);
x_27 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 17);
x_28 = lean_ctor_get_uint8(x_2, sizeof(void*)*7);
x_29 = lean_ctor_get(x_2, 0);
x_30 = lean_ctor_get(x_2, 1);
x_31 = lean_ctor_get(x_2, 2);
x_32 = lean_ctor_get(x_2, 3);
x_33 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 1);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 2);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 3);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 4);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 5);
x_38 = lean_ctor_get(x_2, 4);
x_39 = lean_ctor_get(x_2, 5);
x_40 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 6);
x_41 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 7);
x_42 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_43 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 9);
x_44 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 10);
x_45 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 11);
x_46 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 12);
x_47 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 13);
x_48 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 14);
x_49 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 15);
x_50 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 16);
x_51 = lean_ctor_get(x_2, 6);
x_52 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 17);
x_127 = lean_box(0);
if (x_3 == 0)
{
if (x_28 == 0)
{
goto block_126;
}
else
{
uint8_t x_128; 
x_128 = lean_unbox(x_127);
return x_128;
}
}
else
{
if (x_28 == 0)
{
uint8_t x_129; 
x_129 = lean_unbox(x_127);
return x_129;
}
else
{
goto block_126;
}
}
block_54:
{
uint8_t x_53; 
x_53 = lean_nat_dec_eq(x_26, x_51);
if (x_53 == 0)
{
return x_53;
}
else
{
if (x_27 == 0)
{
if (x_52 == 0)
{
return x_53;
}
else
{
return x_27;
}
}
else
{
return x_52;
}
}
}
block_58:
{
lean_object* x_55; 
x_55 = lean_box(0);
if (x_25 == 0)
{
if (x_50 == 0)
{
goto block_54;
}
else
{
uint8_t x_56; 
x_56 = lean_unbox(x_55);
return x_56;
}
}
else
{
if (x_50 == 0)
{
uint8_t x_57; 
x_57 = lean_unbox(x_55);
return x_57;
}
else
{
goto block_54;
}
}
}
block_62:
{
lean_object* x_59; 
x_59 = lean_box(0);
if (x_24 == 0)
{
if (x_49 == 0)
{
goto block_58;
}
else
{
uint8_t x_60; 
x_60 = lean_unbox(x_59);
return x_60;
}
}
else
{
if (x_49 == 0)
{
uint8_t x_61; 
x_61 = lean_unbox(x_59);
return x_61;
}
else
{
goto block_58;
}
}
}
block_66:
{
lean_object* x_63; 
x_63 = lean_box(0);
if (x_23 == 0)
{
if (x_48 == 0)
{
goto block_62;
}
else
{
uint8_t x_64; 
x_64 = lean_unbox(x_63);
return x_64;
}
}
else
{
if (x_48 == 0)
{
uint8_t x_65; 
x_65 = lean_unbox(x_63);
return x_65;
}
else
{
goto block_62;
}
}
}
block_70:
{
lean_object* x_67; 
x_67 = lean_box(0);
if (x_22 == 0)
{
if (x_47 == 0)
{
goto block_66;
}
else
{
uint8_t x_68; 
x_68 = lean_unbox(x_67);
return x_68;
}
}
else
{
if (x_47 == 0)
{
uint8_t x_69; 
x_69 = lean_unbox(x_67);
return x_69;
}
else
{
goto block_66;
}
}
}
block_74:
{
lean_object* x_71; 
x_71 = lean_box(0);
if (x_21 == 0)
{
if (x_46 == 0)
{
goto block_70;
}
else
{
uint8_t x_72; 
x_72 = lean_unbox(x_71);
return x_72;
}
}
else
{
if (x_46 == 0)
{
uint8_t x_73; 
x_73 = lean_unbox(x_71);
return x_73;
}
else
{
goto block_70;
}
}
}
block_78:
{
lean_object* x_75; 
x_75 = lean_box(0);
if (x_20 == 0)
{
if (x_45 == 0)
{
goto block_74;
}
else
{
uint8_t x_76; 
x_76 = lean_unbox(x_75);
return x_76;
}
}
else
{
if (x_45 == 0)
{
uint8_t x_77; 
x_77 = lean_unbox(x_75);
return x_77;
}
else
{
goto block_74;
}
}
}
block_82:
{
lean_object* x_79; 
x_79 = lean_box(0);
if (x_19 == 0)
{
if (x_44 == 0)
{
goto block_78;
}
else
{
uint8_t x_80; 
x_80 = lean_unbox(x_79);
return x_80;
}
}
else
{
if (x_44 == 0)
{
uint8_t x_81; 
x_81 = lean_unbox(x_79);
return x_81;
}
else
{
goto block_78;
}
}
}
block_86:
{
lean_object* x_83; 
x_83 = lean_box(0);
if (x_18 == 0)
{
if (x_43 == 0)
{
goto block_82;
}
else
{
uint8_t x_84; 
x_84 = lean_unbox(x_83);
return x_84;
}
}
else
{
if (x_43 == 0)
{
uint8_t x_85; 
x_85 = lean_unbox(x_83);
return x_85;
}
else
{
goto block_82;
}
}
}
block_90:
{
lean_object* x_87; 
x_87 = lean_box(0);
if (x_17 == 0)
{
if (x_42 == 0)
{
goto block_86;
}
else
{
uint8_t x_88; 
x_88 = lean_unbox(x_87);
return x_88;
}
}
else
{
if (x_42 == 0)
{
uint8_t x_89; 
x_89 = lean_unbox(x_87);
return x_89;
}
else
{
goto block_86;
}
}
}
block_95:
{
if (x_91 == 0)
{
return x_91;
}
else
{
lean_object* x_92; 
x_92 = lean_box(0);
if (x_16 == 0)
{
if (x_41 == 0)
{
goto block_90;
}
else
{
uint8_t x_93; 
x_93 = lean_unbox(x_92);
return x_93;
}
}
else
{
if (x_41 == 0)
{
uint8_t x_94; 
x_94 = lean_unbox(x_92);
return x_94;
}
else
{
goto block_90;
}
}
}
}
block_101:
{
uint8_t x_96; 
x_96 = lean_nat_dec_eq(x_13, x_38);
if (x_96 == 0)
{
return x_96;
}
else
{
uint8_t x_97; 
x_97 = lean_nat_dec_eq(x_14, x_39);
if (x_97 == 0)
{
return x_97;
}
else
{
lean_object* x_98; 
x_98 = lean_box(0);
if (x_15 == 0)
{
if (x_40 == 0)
{
x_91 = x_97;
goto block_95;
}
else
{
uint8_t x_99; 
x_99 = lean_unbox(x_98);
return x_99;
}
}
else
{
if (x_40 == 0)
{
uint8_t x_100; 
x_100 = lean_unbox(x_98);
return x_100;
}
else
{
x_91 = x_97;
goto block_95;
}
}
}
}
}
block_105:
{
lean_object* x_102; 
x_102 = lean_box(0);
if (x_12 == 0)
{
if (x_37 == 0)
{
goto block_101;
}
else
{
uint8_t x_103; 
x_103 = lean_unbox(x_102);
return x_103;
}
}
else
{
if (x_37 == 0)
{
uint8_t x_104; 
x_104 = lean_unbox(x_102);
return x_104;
}
else
{
goto block_101;
}
}
}
block_109:
{
lean_object* x_106; 
x_106 = lean_box(0);
if (x_11 == 0)
{
if (x_36 == 0)
{
goto block_105;
}
else
{
uint8_t x_107; 
x_107 = lean_unbox(x_106);
return x_107;
}
}
else
{
if (x_36 == 0)
{
uint8_t x_108; 
x_108 = lean_unbox(x_106);
return x_108;
}
else
{
goto block_105;
}
}
}
block_113:
{
lean_object* x_110; 
x_110 = lean_box(0);
if (x_10 == 0)
{
if (x_35 == 0)
{
goto block_109;
}
else
{
uint8_t x_111; 
x_111 = lean_unbox(x_110);
return x_111;
}
}
else
{
if (x_35 == 0)
{
uint8_t x_112; 
x_112 = lean_unbox(x_110);
return x_112;
}
else
{
goto block_109;
}
}
}
block_118:
{
if (x_114 == 0)
{
return x_114;
}
else
{
lean_object* x_115; 
x_115 = lean_box(0);
if (x_9 == 0)
{
if (x_34 == 0)
{
goto block_113;
}
else
{
uint8_t x_116; 
x_116 = lean_unbox(x_115);
return x_116;
}
}
else
{
if (x_34 == 0)
{
uint8_t x_117; 
x_117 = lean_unbox(x_115);
return x_117;
}
else
{
goto block_113;
}
}
}
}
block_126:
{
uint8_t x_119; 
x_119 = lean_nat_dec_eq(x_4, x_29);
if (x_119 == 0)
{
return x_119;
}
else
{
uint8_t x_120; 
x_120 = lean_nat_dec_eq(x_5, x_30);
if (x_120 == 0)
{
return x_120;
}
else
{
uint8_t x_121; 
x_121 = lean_nat_dec_eq(x_6, x_31);
if (x_121 == 0)
{
return x_121;
}
else
{
uint8_t x_122; 
x_122 = lean_nat_dec_eq(x_7, x_32);
if (x_122 == 0)
{
return x_122;
}
else
{
lean_object* x_123; 
x_123 = lean_box(0);
if (x_8 == 0)
{
if (x_33 == 0)
{
x_114 = x_122;
goto block_118;
}
else
{
uint8_t x_124; 
x_124 = lean_unbox(x_123);
return x_124;
}
}
else
{
if (x_33 == 0)
{
uint8_t x_125; 
x_125 = lean_unbox(x_123);
return x_125;
}
else
{
x_114 = x_122;
goto block_118;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Tactics_0__Lean_Grind_beqConfig____x40_Init_Grind_Tactics___hyg_410____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Grind_Tactics_0__Lean_Grind_beqConfig____x40_Init_Grind_Tactics___hyg_410_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_instBEqConfig() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Grind_Tactics_0__Lean_Grind_beqConfig____x40_Init_Grind_Tactics___hyg_410____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindErase() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_1 = lean_mk_string_unchecked("grindErase", 10, 10);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("-", 1, 1);
x_9 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_mk_string_unchecked("ident", 5, 5);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_9);
lean_ctor_set(x_13, 2, x_12);
x_14 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 2, x_13);
return x_14;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindLemma() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_1 = lean_mk_string_unchecked("grindLemma", 10, 10);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("optional", 8, 8);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = l_Lean_Parser_Attr_grindMod;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_mk_string_unchecked("ident", 5, 5);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
x_16 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_5);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindParam() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_1 = lean_mk_string_unchecked("grindParam", 10, 10);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("orelse", 6, 6);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = l_Lean_Parser_Tactic_grindErase;
x_9 = l_Lean_Parser_Tactic_grindLemma;
x_10 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
x_11 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 2, x_10);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("grind", 5, 5);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_11);
x_12 = l_Lean_Parser_Tactic_optConfig;
lean_inc(x_8);
x_13 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_12);
x_14 = lean_mk_string_unchecked("optional", 8, 8);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = lean_mk_string_unchecked(" only", 5, 5);
x_17 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_unbox(x_9);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_18);
lean_inc(x_15);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_17);
lean_inc(x_8);
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_13);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_mk_string_unchecked(" [", 2, 2);
x_22 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_mk_string_unchecked("withoutPosition", 15, 15);
x_24 = l_Lean_Name_mkStr1(x_23);
x_25 = l_Lean_Parser_Tactic_grindParam;
x_26 = lean_mk_string_unchecked(",", 1, 1);
x_27 = lean_mk_string_unchecked(", ", 2, 2);
x_28 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(10, 3, 1);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_29, 2, x_28);
x_30 = lean_unbox(x_9);
lean_ctor_set_uint8(x_29, sizeof(void*)*3, x_30);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_29);
lean_inc(x_8);
x_32 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_32, 0, x_8);
lean_ctor_set(x_32, 1, x_22);
lean_ctor_set(x_32, 2, x_31);
x_33 = lean_mk_string_unchecked("]", 1, 1);
x_34 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_inc(x_8);
x_35 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_32);
lean_ctor_set(x_35, 2, x_34);
lean_inc(x_15);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_15);
lean_ctor_set(x_36, 1, x_35);
lean_inc(x_8);
x_37 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_37, 0, x_8);
lean_ctor_set(x_37, 1, x_20);
lean_ctor_set(x_37, 2, x_36);
x_38 = lean_mk_string_unchecked("on_failure ", 11, 11);
x_39 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_mk_string_unchecked("term", 4, 4);
x_41 = l_Lean_Name_mkStr1(x_40);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
lean_inc(x_8);
x_44 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_44, 0, x_8);
lean_ctor_set(x_44, 1, x_39);
lean_ctor_set(x_44, 2, x_43);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_15);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_46, 0, x_8);
lean_ctor_set(x_46, 1, x_37);
lean_ctor_set(x_46, 2, x_45);
x_47 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_47, 0, x_5);
lean_ctor_set(x_47, 1, x_6);
lean_ctor_set(x_47, 2, x_46);
return x_47;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindTrace() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("grindTrace", 10, 10);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("grind\?", 6, 6);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = l_Lean_Parser_Tactic_optConfig;
lean_inc(x_8);
x_14 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_mk_string_unchecked("optional", 8, 8);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = lean_mk_string_unchecked(" only", 5, 5);
x_18 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_unbox(x_10);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_19);
lean_inc(x_16);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_18);
lean_inc(x_8);
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_mk_string_unchecked(" [", 2, 2);
x_23 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_mk_string_unchecked("withoutPosition", 15, 15);
x_25 = l_Lean_Name_mkStr1(x_24);
x_26 = l_Lean_Parser_Tactic_grindParam;
x_27 = lean_mk_string_unchecked(",", 1, 1);
x_28 = lean_mk_string_unchecked(", ", 2, 2);
x_29 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(10, 3, 1);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_27);
lean_ctor_set(x_30, 2, x_29);
x_31 = lean_unbox(x_10);
lean_ctor_set_uint8(x_30, sizeof(void*)*3, x_31);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_30);
lean_inc(x_8);
x_33 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_33, 0, x_8);
lean_ctor_set(x_33, 1, x_23);
lean_ctor_set(x_33, 2, x_32);
x_34 = lean_mk_string_unchecked("]", 1, 1);
x_35 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_inc(x_8);
x_36 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_36, 0, x_8);
lean_ctor_set(x_36, 1, x_33);
lean_ctor_set(x_36, 2, x_35);
lean_inc(x_16);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_16);
lean_ctor_set(x_37, 1, x_36);
lean_inc(x_8);
x_38 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_38, 0, x_8);
lean_ctor_set(x_38, 1, x_21);
lean_ctor_set(x_38, 2, x_37);
x_39 = lean_mk_string_unchecked("on_failure ", 11, 11);
x_40 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_mk_string_unchecked("term", 4, 4);
x_42 = l_Lean_Name_mkStr1(x_41);
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_inc(x_8);
x_45 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_45, 0, x_8);
lean_ctor_set(x_45, 1, x_40);
lean_ctor_set(x_45, 2, x_44);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_16);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_47, 0, x_8);
lean_ctor_set(x_47, 1, x_38);
lean_ctor_set(x_47, 2, x_46);
x_48 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_48, 0, x_5);
lean_ctor_set(x_48, 1, x_6);
lean_ctor_set(x_48, 2, x_47);
return x_48;
}
}
lean_object* initialize_Init_Tactics(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_Tactics(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Tactics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_resetGrindAttrs = _init_l_Lean_Parser_resetGrindAttrs();
lean_mark_persistent(l_Lean_Parser_resetGrindAttrs);
l_Lean_Parser_Attr_grindEq = _init_l_Lean_Parser_Attr_grindEq();
lean_mark_persistent(l_Lean_Parser_Attr_grindEq);
l_Lean_Parser_Attr_grindEqBoth = _init_l_Lean_Parser_Attr_grindEqBoth();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqBoth);
l_Lean_Parser_Attr_grindEqRhs = _init_l_Lean_Parser_Attr_grindEqRhs();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqRhs);
l_Lean_Parser_Attr_grindEqBwd = _init_l_Lean_Parser_Attr_grindEqBwd();
lean_mark_persistent(l_Lean_Parser_Attr_grindEqBwd);
l_Lean_Parser_Attr_grindBwd = _init_l_Lean_Parser_Attr_grindBwd();
lean_mark_persistent(l_Lean_Parser_Attr_grindBwd);
l_Lean_Parser_Attr_grindFwd = _init_l_Lean_Parser_Attr_grindFwd();
lean_mark_persistent(l_Lean_Parser_Attr_grindFwd);
l_Lean_Parser_Attr_grindRL = _init_l_Lean_Parser_Attr_grindRL();
lean_mark_persistent(l_Lean_Parser_Attr_grindRL);
l_Lean_Parser_Attr_grindLR = _init_l_Lean_Parser_Attr_grindLR();
lean_mark_persistent(l_Lean_Parser_Attr_grindLR);
l_Lean_Parser_Attr_grindUsr = _init_l_Lean_Parser_Attr_grindUsr();
lean_mark_persistent(l_Lean_Parser_Attr_grindUsr);
l_Lean_Parser_Attr_grindCases = _init_l_Lean_Parser_Attr_grindCases();
lean_mark_persistent(l_Lean_Parser_Attr_grindCases);
l_Lean_Parser_Attr_grindCasesEager = _init_l_Lean_Parser_Attr_grindCasesEager();
lean_mark_persistent(l_Lean_Parser_Attr_grindCasesEager);
l_Lean_Parser_Attr_grindIntro = _init_l_Lean_Parser_Attr_grindIntro();
lean_mark_persistent(l_Lean_Parser_Attr_grindIntro);
l_Lean_Parser_Attr_grindExt = _init_l_Lean_Parser_Attr_grindExt();
lean_mark_persistent(l_Lean_Parser_Attr_grindExt);
l_Lean_Parser_Attr_grindMod = _init_l_Lean_Parser_Attr_grindMod();
lean_mark_persistent(l_Lean_Parser_Attr_grindMod);
l_Lean_Parser_Attr_grind = _init_l_Lean_Parser_Attr_grind();
lean_mark_persistent(l_Lean_Parser_Attr_grind);
l_Lean_Grind_instInhabitedConfig = _init_l_Lean_Grind_instInhabitedConfig();
lean_mark_persistent(l_Lean_Grind_instInhabitedConfig);
l_Lean_Grind_instBEqConfig = _init_l_Lean_Grind_instBEqConfig();
lean_mark_persistent(l_Lean_Grind_instBEqConfig);
l_Lean_Parser_Tactic_grindErase = _init_l_Lean_Parser_Tactic_grindErase();
lean_mark_persistent(l_Lean_Parser_Tactic_grindErase);
l_Lean_Parser_Tactic_grindLemma = _init_l_Lean_Parser_Tactic_grindLemma();
lean_mark_persistent(l_Lean_Parser_Tactic_grindLemma);
l_Lean_Parser_Tactic_grindParam = _init_l_Lean_Parser_Tactic_grindParam();
lean_mark_persistent(l_Lean_Parser_Tactic_grindParam);
l_Lean_Parser_Tactic_grind = _init_l_Lean_Parser_Tactic_grind();
lean_mark_persistent(l_Lean_Parser_Tactic_grind);
l_Lean_Parser_Tactic_grindTrace = _init_l_Lean_Parser_Tactic_grindTrace();
lean_mark_persistent(l_Lean_Parser_Tactic_grindTrace);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
