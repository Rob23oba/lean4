// Lean compiler output
// Module: Init.Ext
// Imports: Init.Data.ToString.Macro Init.TacticsExtra Init.RCases
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
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_extFlat;
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Ext_tacticExt1______;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Ext_ext;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_ext;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Ext_applyExtTheorem;
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_extIff;
static lean_object* _init_l_Lean_Parser_Attr_extIff() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_1 = lean_mk_string_unchecked("extIff", 6, 6);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Attr", 4, 4);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("atomic", 6, 6);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("andthen", 7, 7);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("(", 1, 1);
x_11 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_mk_string_unchecked("iff", 3, 3);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_14, 0, x_12);
x_15 = lean_unbox(x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_15);
lean_inc(x_9);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_14);
x_17 = lean_mk_string_unchecked(" := ", 4, 4);
x_18 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_inc(x_9);
x_19 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_mk_string_unchecked("false", 5, 5);
x_21 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_unbox(x_13);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_22);
lean_inc(x_9);
x_23 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_23, 0, x_9);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set(x_23, 2, x_21);
x_24 = lean_mk_string_unchecked(")", 1, 1);
x_25 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_26, 0, x_9);
lean_ctor_set(x_26, 1, x_23);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_7);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_5);
lean_ctor_set(x_28, 2, x_27);
return x_28;
}
}
static lean_object* _init_l_Lean_Parser_Attr_extFlat() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_1 = lean_mk_string_unchecked("extFlat", 7, 7);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Attr", 4, 4);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("atomic", 6, 6);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("andthen", 7, 7);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("(", 1, 1);
x_11 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_mk_string_unchecked("flat", 4, 4);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_14, 0, x_12);
x_15 = lean_unbox(x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_15);
lean_inc(x_9);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_14);
x_17 = lean_mk_string_unchecked(" := ", 4, 4);
x_18 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_inc(x_9);
x_19 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_mk_string_unchecked("false", 5, 5);
x_21 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_unbox(x_13);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_22);
lean_inc(x_9);
x_23 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_23, 0, x_9);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set(x_23, 2, x_21);
x_24 = lean_mk_string_unchecked(")", 1, 1);
x_25 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_26, 0, x_9);
lean_ctor_set(x_26, 1, x_23);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_7);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_5);
lean_ctor_set(x_28, 2, x_27);
return x_28;
}
}
static lean_object* _init_l_Lean_Parser_Attr_ext() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Attr", 4, 4);
x_4 = lean_mk_string_unchecked("ext", 3, 3);
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
x_14 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_Parser_Attr_extIff;
lean_inc(x_16);
lean_inc(x_8);
x_18 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_17);
lean_inc(x_13);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
lean_inc(x_8);
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_10);
lean_ctor_set(x_20, 2, x_19);
x_21 = l_Lean_Parser_Attr_extFlat;
lean_inc(x_16);
lean_inc(x_8);
x_22 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_16);
lean_ctor_set(x_22, 2, x_21);
lean_inc(x_13);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_13);
lean_ctor_set(x_23, 1, x_22);
lean_inc(x_8);
x_24 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_mk_string_unchecked("prio", 4, 4);
x_26 = l_Lean_Name_mkStr1(x_25);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
lean_inc(x_8);
x_29 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_29, 0, x_8);
lean_ctor_set(x_29, 1, x_16);
lean_ctor_set(x_29, 2, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_13);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_31, 0, x_8);
lean_ctor_set(x_31, 1, x_24);
lean_ctor_set(x_31, 2, x_30);
x_32 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_32, 0, x_5);
lean_ctor_set(x_32, 1, x_6);
lean_ctor_set(x_32, 2, x_31);
return x_32;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Ext_ext() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Elab", 4, 4);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("Ext", 3, 3);
x_5 = lean_mk_string_unchecked("ext", 3, 3);
lean_inc(x_5);
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(1022u);
x_8 = lean_mk_string_unchecked("andthen", 7, 7);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_5);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("many", 4, 4);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_mk_string_unchecked("colGt", 5, 5);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_19 = l_Lean_Name_mkStr1(x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_inc(x_9);
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_9);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_mk_string_unchecked("rintroPat", 9, 9);
x_23 = l_Lean_Name_mkStr1(x_22);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_inc(x_9);
x_26 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_26, 0, x_9);
lean_ctor_set(x_26, 1, x_21);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_26);
lean_inc(x_9);
x_28 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_28, 0, x_9);
lean_ctor_set(x_28, 1, x_11);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_mk_string_unchecked("optional", 8, 8);
x_30 = l_Lean_Name_mkStr1(x_29);
x_31 = lean_mk_string_unchecked(" : ", 3, 3);
x_32 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_mk_string_unchecked("num", 3, 3);
x_34 = l_Lean_Name_mkStr1(x_33);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_inc(x_9);
x_36 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_36, 0, x_9);
lean_ctor_set(x_36, 1, x_32);
lean_ctor_set(x_36, 2, x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_30);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_38, 0, x_9);
lean_ctor_set(x_38, 1, x_28);
lean_ctor_set(x_38, 2, x_37);
x_39 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_39, 0, x_6);
lean_ctor_set(x_39, 1, x_7);
lean_ctor_set(x_39, 2, x_38);
return x_39;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Ext_applyExtTheorem() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Elab", 4, 4);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("Ext", 3, 3);
x_5 = lean_mk_string_unchecked("applyExtTheorem", 15, 15);
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(1024u);
x_8 = lean_mk_string_unchecked("apply_ext_theorem", 17, 17);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_10, 0, x_8);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_11);
x_12 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_10);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Ext_tacticExt1______() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Elab", 4, 4);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("Ext", 3, 3);
x_5 = lean_mk_string_unchecked("tacticExt1___", 13, 13);
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(1022u);
x_8 = lean_mk_string_unchecked("andthen", 7, 7);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("ext1", 4, 4);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_12, 0, x_10);
x_13 = lean_unbox(x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_13);
x_14 = lean_mk_string_unchecked("many", 4, 4);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = lean_mk_string_unchecked("colGt", 5, 5);
x_17 = l_Lean_Name_mkStr1(x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_20 = l_Lean_Name_mkStr1(x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_inc(x_9);
x_22 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_22, 0, x_9);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_mk_string_unchecked("rintroPat", 9, 9);
x_24 = l_Lean_Name_mkStr1(x_23);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
lean_inc(x_9);
x_27 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_27, 0, x_9);
lean_ctor_set(x_27, 1, x_22);
lean_ctor_set(x_27, 2, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_15);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_29, 0, x_9);
lean_ctor_set(x_29, 1, x_12);
lean_ctor_set(x_29, 2, x_28);
x_30 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_30, 0, x_6);
lean_ctor_set(x_30, 1, x_7);
lean_ctor_set(x_30, 2, x_29);
return x_30;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Elab", 4, 4);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("Ext", 3, 3);
x_8 = lean_mk_string_unchecked("tacticExt1___", 13, 13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Name_mkStr5(x_4, x_5, x_6, x_7, x_8);
lean_inc(x_1);
x_10 = l_Lean_Syntax_isOfKind(x_1, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_11 = lean_box(1);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
lean_dec(x_1);
x_15 = l_Lean_Syntax_getArgs(x_14);
lean_dec(x_14);
x_16 = l_Array_isEmpty___redArg(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_17 = lean_ctor_get(x_2, 5);
x_18 = l_Lean_SourceInfo_fromRef(x_17, x_16);
x_19 = lean_mk_string_unchecked("Parser", 6, 6);
x_20 = lean_mk_string_unchecked("tactic_<;>_", 11, 11);
lean_inc(x_6);
lean_inc(x_19);
lean_inc(x_4);
x_21 = l_Lean_Name_mkStr4(x_4, x_19, x_6, x_20);
x_22 = lean_mk_string_unchecked("applyExtTheorem", 15, 15);
lean_inc(x_6);
lean_inc(x_4);
x_23 = l_Lean_Name_mkStr5(x_4, x_5, x_6, x_7, x_22);
x_24 = lean_mk_string_unchecked("apply_ext_theorem", 17, 17);
lean_inc(x_18);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_24);
lean_inc(x_18);
x_26 = l_Lean_Syntax_node1(x_18, x_23, x_25);
x_27 = lean_mk_string_unchecked("<;>", 3, 3);
lean_inc(x_18);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_mk_string_unchecked("rintro", 6, 6);
lean_inc(x_29);
x_30 = l_Lean_Name_mkStr4(x_4, x_19, x_6, x_29);
lean_inc(x_18);
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_18);
lean_ctor_set(x_31, 1, x_29);
x_32 = lean_mk_string_unchecked("null", 4, 4);
x_33 = l_Lean_Name_mkStr1(x_32);
x_34 = l_Array_mkArray0(lean_box(0));
lean_inc(x_34);
x_35 = l_Array_append(lean_box(0), x_34, x_15);
lean_dec(x_15);
lean_inc(x_33);
lean_inc(x_18);
x_36 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_36, 0, x_18);
lean_ctor_set(x_36, 1, x_33);
lean_ctor_set(x_36, 2, x_35);
lean_inc(x_18);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_18);
lean_ctor_set(x_37, 1, x_33);
lean_ctor_set(x_37, 2, x_34);
lean_inc(x_18);
x_38 = l_Lean_Syntax_node3(x_18, x_30, x_31, x_36, x_37);
x_39 = l_Lean_Syntax_node3(x_18, x_21, x_26, x_28, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_3);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_15);
x_41 = lean_ctor_get(x_2, 5);
x_42 = lean_box(0);
x_43 = lean_unbox(x_42);
x_44 = l_Lean_SourceInfo_fromRef(x_41, x_43);
x_45 = lean_mk_string_unchecked("Parser", 6, 6);
x_46 = lean_mk_string_unchecked("tactic_<;>_", 11, 11);
lean_inc(x_6);
lean_inc(x_45);
lean_inc(x_4);
x_47 = l_Lean_Name_mkStr4(x_4, x_45, x_6, x_46);
x_48 = lean_mk_string_unchecked("applyExtTheorem", 15, 15);
lean_inc(x_6);
lean_inc(x_4);
x_49 = l_Lean_Name_mkStr5(x_4, x_5, x_6, x_7, x_48);
x_50 = lean_mk_string_unchecked("apply_ext_theorem", 17, 17);
lean_inc(x_44);
x_51 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_51, 0, x_44);
lean_ctor_set(x_51, 1, x_50);
lean_inc(x_44);
x_52 = l_Lean_Syntax_node1(x_44, x_49, x_51);
x_53 = lean_mk_string_unchecked("<;>", 3, 3);
lean_inc(x_44);
x_54 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_54, 0, x_44);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_mk_string_unchecked("intros", 6, 6);
lean_inc(x_55);
x_56 = l_Lean_Name_mkStr4(x_4, x_45, x_6, x_55);
lean_inc(x_44);
x_57 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_57, 0, x_44);
lean_ctor_set(x_57, 1, x_55);
x_58 = lean_mk_string_unchecked("null", 4, 4);
x_59 = l_Lean_Name_mkStr1(x_58);
x_60 = l_Array_mkArray0(lean_box(0));
lean_inc(x_44);
x_61 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_61, 0, x_44);
lean_ctor_set(x_61, 1, x_59);
lean_ctor_set(x_61, 2, x_60);
lean_inc(x_44);
x_62 = l_Lean_Syntax_node2(x_44, x_56, x_57, x_61);
x_63 = l_Lean_Syntax_node3(x_44, x_47, x_52, x_54, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_3);
return x_64;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin, lean_object*);
lean_object* initialize_Init_TacticsExtra(uint8_t builtin, lean_object*);
lean_object* initialize_Init_RCases(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Ext(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString_Macro(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_TacticsExtra(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_RCases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Attr_extIff = _init_l_Lean_Parser_Attr_extIff();
lean_mark_persistent(l_Lean_Parser_Attr_extIff);
l_Lean_Parser_Attr_extFlat = _init_l_Lean_Parser_Attr_extFlat();
lean_mark_persistent(l_Lean_Parser_Attr_extFlat);
l_Lean_Parser_Attr_ext = _init_l_Lean_Parser_Attr_ext();
lean_mark_persistent(l_Lean_Parser_Attr_ext);
l_Lean_Elab_Tactic_Ext_ext = _init_l_Lean_Elab_Tactic_Ext_ext();
lean_mark_persistent(l_Lean_Elab_Tactic_Ext_ext);
l_Lean_Elab_Tactic_Ext_applyExtTheorem = _init_l_Lean_Elab_Tactic_Ext_applyExtTheorem();
lean_mark_persistent(l_Lean_Elab_Tactic_Ext_applyExtTheorem);
l_Lean_Elab_Tactic_Ext_tacticExt1______ = _init_l_Lean_Elab_Tactic_Ext_tacticExt1______();
lean_mark_persistent(l_Lean_Elab_Tactic_Ext_tacticExt1______);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
