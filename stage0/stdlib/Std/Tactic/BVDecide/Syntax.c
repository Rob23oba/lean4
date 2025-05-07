// Lean compiler output
// Module: Std.Tactic.BVDecide.Syntax
// Imports: Init.Notation Init.Simproc
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
uint8_t l_Lean_Syntax_matchesIdent(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_optConfig;
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_bvDecide;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_bvCheck;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_bvNormalize;
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_bvTrace;
extern lean_object* l_Lean_Parser_Tactic_simpPre;
extern lean_object* l_Lean_Parser_Tactic_simpPost;
LEAN_EXPORT lean_object* l_Lean_Parser_bv__normalize;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_bvNormalizeProcBuiltinAttr;
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Syntax_node8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Parser_Tactic_bvCheck() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("bvCheck", 7, 7);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("bv_check ", 9, 9);
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
x_15 = lean_mk_string_unchecked("str", 3, 3);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_17);
x_19 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_6);
lean_ctor_set(x_19, 2, x_18);
return x_19;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_bvDecide() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("bvDecide", 8, 8);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("bv_decide", 9, 9);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = l_Lean_Parser_Tactic_optConfig;
x_14 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_6);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_bvTrace() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("bvTrace", 7, 7);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("bv_decide\?", 10, 10);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = l_Lean_Parser_Tactic_optConfig;
x_14 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_6);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_bvNormalize() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("bvNormalize", 11, 11);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("bv_normalize", 12, 12);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = l_Lean_Parser_Tactic_optConfig;
x_14 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_6);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
}
static lean_object* _init_l_Lean_Parser_bv__normalize() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("bv_normalize", 12, 12);
lean_inc(x_3);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
x_5 = lean_unsigned_to_nat(1022u);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_3);
x_10 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_10);
x_11 = lean_mk_string_unchecked("optional", 8, 8);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_mk_string_unchecked("orelse", 6, 6);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = l_Lean_Parser_Tactic_simpPre;
x_16 = l_Lean_Parser_Tactic_simpPost;
lean_inc(x_14);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_16);
lean_inc(x_12);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
lean_inc(x_7);
x_19 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_9);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_mk_string_unchecked("patternIgnore", 13, 13);
x_21 = l_Lean_Name_mkStr1(x_20);
x_22 = lean_mk_string_unchecked("← ", 4, 2);
x_23 = lean_mk_string_unchecked("token", 5, 5);
lean_inc(x_22);
lean_inc(x_23);
x_24 = l_Lean_Name_mkStr2(x_23, x_22);
lean_inc(x_22);
x_25 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_25, 0, x_22);
x_26 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_mk_string_unchecked("<- ", 3, 3);
lean_inc(x_27);
x_28 = l_Lean_Name_mkStr2(x_23, x_27);
lean_inc(x_27);
x_29 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_29, 0, x_27);
x_30 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_30, 2, x_29);
x_31 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_31, 0, x_14);
lean_ctor_set(x_31, 1, x_26);
lean_ctor_set(x_31, 2, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_21);
lean_ctor_set(x_32, 1, x_31);
lean_inc(x_12);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_12);
lean_ctor_set(x_33, 1, x_32);
lean_inc(x_7);
x_34 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_19);
lean_ctor_set(x_34, 2, x_33);
x_35 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_36 = l_Lean_Name_mkStr1(x_35);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_mk_string_unchecked("prio", 4, 4);
x_39 = l_Lean_Name_mkStr1(x_38);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
lean_inc(x_7);
x_42 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_42, 0, x_7);
lean_ctor_set(x_42, 1, x_37);
lean_ctor_set(x_42, 2, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_12);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_44, 0, x_7);
lean_ctor_set(x_44, 1, x_34);
lean_ctor_set(x_44, 2, x_43);
x_45 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_45, 0, x_4);
lean_ctor_set(x_45, 1, x_5);
lean_ctor_set(x_45, 2, x_44);
return x_45;
}
}
static lean_object* _init_l_Lean_Parser_bvNormalizeProcBuiltinAttr() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("bvNormalizeProcBuiltinAttr", 26, 26);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
x_5 = lean_unsigned_to_nat(1022u);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("builtin_bv_normalize_proc", 25, 25);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_10, 0, x_8);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_11);
x_12 = lean_mk_string_unchecked("optional", 8, 8);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_mk_string_unchecked("orelse", 6, 6);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = l_Lean_Parser_Tactic_simpPre;
x_17 = l_Lean_Parser_Tactic_simpPost;
x_18 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_10);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_5);
lean_ctor_set(x_21, 2, x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_30 = lean_mk_string_unchecked("Lean", 4, 4);
x_31 = lean_mk_string_unchecked("Parser", 6, 6);
x_71 = lean_mk_string_unchecked("command__Builtin_simproc__[_]_(_):=_", 36, 36);
lean_inc(x_31);
lean_inc(x_30);
x_72 = l_Lean_Name_mkStr3(x_30, x_31, x_71);
lean_inc(x_1);
x_73 = l_Lean_Syntax_isOfKind(x_1, x_72);
lean_dec(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_1);
x_74 = lean_box(1);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_3);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_145; uint8_t x_146; 
x_76 = lean_unsigned_to_nat(0u);
x_145 = l_Lean_Syntax_getArg(x_1, x_76);
x_146 = l_Lean_Syntax_isNone(x_145);
if (x_146 == 0)
{
lean_object* x_147; uint8_t x_148; 
x_147 = lean_unsigned_to_nat(1u);
lean_inc(x_145);
x_148 = l_Lean_Syntax_matchesNull(x_145, x_147);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; 
lean_dec(x_145);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_1);
x_149 = lean_box(1);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_3);
return x_150;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_151 = l_Lean_Syntax_getArg(x_145, x_76);
lean_dec(x_145);
x_152 = lean_mk_string_unchecked("Command", 7, 7);
x_153 = lean_mk_string_unchecked("docComment", 10, 10);
lean_inc(x_31);
lean_inc(x_30);
x_154 = l_Lean_Name_mkStr4(x_30, x_31, x_152, x_153);
lean_inc(x_151);
x_155 = l_Lean_Syntax_isOfKind(x_151, x_154);
lean_dec(x_154);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_151);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_1);
x_156 = lean_box(1);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_3);
return x_157;
}
else
{
lean_object* x_158; 
x_158 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_158, 0, x_151);
x_124 = x_158;
x_125 = x_2;
x_126 = x_3;
goto block_144;
}
}
}
else
{
lean_object* x_159; 
lean_dec(x_145);
x_159 = lean_box(0);
x_124 = x_159;
x_125 = x_2;
x_126 = x_3;
goto block_144;
}
block_123:
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_unsigned_to_nat(4u);
x_86 = l_Lean_Syntax_getArg(x_1, x_85);
lean_inc(x_86);
x_87 = l_Lean_Syntax_matchesNull(x_86, x_81);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_86);
lean_dec(x_82);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_1);
x_88 = lean_box(1);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_84);
return x_89;
}
else
{
lean_object* x_90; uint8_t x_91; 
x_90 = l_Lean_Syntax_getArg(x_86, x_80);
lean_dec(x_86);
lean_inc(x_90);
x_91 = l_Lean_Syntax_matchesNull(x_90, x_80);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_90);
lean_dec(x_82);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_1);
x_92 = lean_box(1);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_84);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_94 = l_Lean_Syntax_getArg(x_90, x_76);
lean_dec(x_90);
x_95 = lean_mk_string_unchecked("bv_normalize", 12, 12);
x_96 = l_Lean_Name_mkStr1(x_95);
x_97 = l_Lean_Syntax_matchesIdent(x_94, x_96);
lean_dec(x_94);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_82);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_1);
x_98 = lean_box(1);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_84);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_100 = lean_unsigned_to_nat(5u);
x_101 = l_Lean_Syntax_getArg(x_1, x_100);
x_102 = lean_mk_string_unchecked("ident", 5, 5);
x_103 = l_Lean_Name_mkStr1(x_102);
lean_inc(x_101);
x_104 = l_Lean_Syntax_isOfKind(x_101, x_103);
lean_dec(x_103);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_101);
lean_dec(x_82);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_1);
x_105 = lean_box(1);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_84);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_107 = lean_unsigned_to_nat(7u);
x_108 = l_Lean_Syntax_getArg(x_1, x_107);
x_109 = lean_unsigned_to_nat(10u);
x_110 = l_Lean_Syntax_getArg(x_1, x_109);
lean_dec(x_1);
x_111 = lean_ctor_get(x_83, 5);
x_112 = lean_box(0);
x_113 = lean_unbox(x_112);
x_114 = l_Lean_SourceInfo_fromRef(x_111, x_113);
x_115 = lean_mk_string_unchecked("null", 4, 4);
x_116 = l_Lean_Name_mkStr1(x_115);
x_117 = lean_mk_string_unchecked("command_Builtin_simproc_decl_(_):=_", 35, 35);
lean_inc(x_31);
lean_inc(x_30);
x_118 = l_Lean_Name_mkStr3(x_30, x_31, x_117);
x_119 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_120; 
x_120 = l_Array_empty(lean_box(0));
x_32 = x_119;
x_33 = x_77;
x_34 = x_78;
x_35 = x_110;
x_36 = x_114;
x_37 = x_84;
x_38 = x_108;
x_39 = x_118;
x_40 = x_82;
x_41 = x_116;
x_42 = x_101;
x_43 = x_120;
goto block_70;
}
else
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_79, 0);
lean_inc(x_121);
lean_dec(x_79);
x_122 = l_Array_mkArray1___redArg(x_121);
x_32 = x_119;
x_33 = x_77;
x_34 = x_78;
x_35 = x_110;
x_36 = x_114;
x_37 = x_84;
x_38 = x_108;
x_39 = x_118;
x_40 = x_82;
x_41 = x_116;
x_42 = x_101;
x_43 = x_122;
goto block_70;
}
}
}
}
}
}
block_144:
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_127 = lean_unsigned_to_nat(1u);
x_128 = l_Lean_Syntax_getArg(x_1, x_127);
x_129 = lean_mk_string_unchecked("Term", 4, 4);
x_130 = lean_mk_string_unchecked("attrKind", 8, 8);
lean_inc(x_129);
lean_inc(x_31);
lean_inc(x_30);
x_131 = l_Lean_Name_mkStr4(x_30, x_31, x_129, x_130);
lean_inc(x_128);
x_132 = l_Lean_Syntax_isOfKind(x_128, x_131);
lean_dec(x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; 
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_124);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_1);
x_133 = lean_box(1);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_126);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_135 = lean_unsigned_to_nat(3u);
x_136 = l_Lean_Syntax_getArg(x_1, x_135);
x_137 = l_Lean_Syntax_isNone(x_136);
if (x_137 == 0)
{
uint8_t x_138; 
lean_inc(x_136);
x_138 = l_Lean_Syntax_matchesNull(x_136, x_127);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; 
lean_dec(x_136);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_124);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_1);
x_139 = lean_box(1);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_126);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; 
x_141 = l_Lean_Syntax_getArg(x_136, x_76);
lean_dec(x_136);
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_141);
x_77 = x_129;
x_78 = x_128;
x_79 = x_124;
x_80 = x_127;
x_81 = x_135;
x_82 = x_142;
x_83 = x_125;
x_84 = x_126;
goto block_123;
}
}
else
{
lean_object* x_143; 
lean_dec(x_136);
x_143 = lean_box(0);
x_77 = x_129;
x_78 = x_128;
x_79 = x_124;
x_80 = x_127;
x_81 = x_135;
x_82 = x_143;
x_83 = x_125;
x_84 = x_126;
goto block_123;
}
}
}
}
block_29:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = l_Array_append(lean_box(0), x_4, x_17);
lean_dec(x_17);
lean_inc(x_16);
lean_inc(x_5);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_18);
lean_inc(x_5);
x_20 = l_Lean_Syntax_node2(x_5, x_8, x_10, x_19);
lean_inc(x_5);
x_21 = l_Lean_Syntax_node2(x_5, x_7, x_13, x_20);
lean_inc(x_16);
lean_inc(x_5);
x_22 = l_Lean_Syntax_node1(x_5, x_16, x_21);
x_23 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_5);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_5);
lean_ctor_set(x_24, 1, x_23);
lean_inc(x_16);
lean_inc(x_5);
x_25 = l_Lean_Syntax_node1(x_5, x_16, x_9);
lean_inc(x_5);
x_26 = l_Lean_Syntax_node5(x_5, x_6, x_11, x_15, x_22, x_24, x_25);
x_27 = l_Lean_Syntax_node2(x_5, x_16, x_12, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_14);
return x_28;
}
block_70:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_inc(x_32);
x_44 = l_Array_append(lean_box(0), x_32, x_43);
lean_dec(x_43);
lean_inc(x_41);
lean_inc(x_36);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_36);
lean_ctor_set(x_45, 1, x_41);
lean_ctor_set(x_45, 2, x_44);
x_46 = lean_mk_string_unchecked("builtin_simproc_decl", 20, 20);
lean_inc(x_36);
x_47 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_36);
x_49 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_49, 0, x_36);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_36);
x_51 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_51, 0, x_36);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_36);
x_53 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_53, 0, x_36);
lean_ctor_set(x_53, 1, x_52);
lean_inc(x_42);
lean_inc(x_36);
x_54 = l_Lean_Syntax_node8(x_36, x_39, x_45, x_47, x_42, x_49, x_38, x_51, x_53, x_35);
x_55 = lean_mk_string_unchecked("Command", 7, 7);
x_56 = lean_mk_string_unchecked("attribute", 9, 9);
lean_inc(x_56);
lean_inc(x_31);
lean_inc(x_30);
x_57 = l_Lean_Name_mkStr4(x_30, x_31, x_55, x_56);
lean_inc(x_36);
x_58 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_58, 0, x_36);
lean_ctor_set(x_58, 1, x_56);
x_59 = lean_mk_string_unchecked("[", 1, 1);
lean_inc(x_36);
x_60 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_60, 0, x_36);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_mk_string_unchecked("attrInstance", 12, 12);
lean_inc(x_31);
lean_inc(x_30);
x_62 = l_Lean_Name_mkStr4(x_30, x_31, x_33, x_61);
x_63 = lean_mk_string_unchecked("bvNormalizeProcBuiltinAttr", 26, 26);
x_64 = l_Lean_Name_mkStr3(x_30, x_31, x_63);
x_65 = lean_mk_string_unchecked("builtin_bv_normalize_proc", 25, 25);
lean_inc(x_36);
x_66 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_66, 0, x_36);
lean_ctor_set(x_66, 1, x_65);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_67; 
x_67 = l_Array_empty(lean_box(0));
x_4 = x_32;
x_5 = x_36;
x_6 = x_57;
x_7 = x_62;
x_8 = x_64;
x_9 = x_42;
x_10 = x_66;
x_11 = x_58;
x_12 = x_54;
x_13 = x_34;
x_14 = x_37;
x_15 = x_60;
x_16 = x_41;
x_17 = x_67;
goto block_29;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_40, 0);
lean_inc(x_68);
lean_dec(x_40);
x_69 = l_Array_mkArray1___redArg(x_68);
x_4 = x_32;
x_5 = x_36;
x_6 = x_57;
x_7 = x_62;
x_8 = x_64;
x_9 = x_42;
x_10 = x_66;
x_11 = x_58;
x_12 = x_54;
x_13 = x_34;
x_14 = x_37;
x_15 = x_60;
x_16 = x_41;
x_17 = x_69;
goto block_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init_Notation(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Simproc(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Syntax(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Notation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Simproc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_bvCheck = _init_l_Lean_Parser_Tactic_bvCheck();
lean_mark_persistent(l_Lean_Parser_Tactic_bvCheck);
l_Lean_Parser_Tactic_bvDecide = _init_l_Lean_Parser_Tactic_bvDecide();
lean_mark_persistent(l_Lean_Parser_Tactic_bvDecide);
l_Lean_Parser_Tactic_bvTrace = _init_l_Lean_Parser_Tactic_bvTrace();
lean_mark_persistent(l_Lean_Parser_Tactic_bvTrace);
l_Lean_Parser_Tactic_bvNormalize = _init_l_Lean_Parser_Tactic_bvNormalize();
lean_mark_persistent(l_Lean_Parser_Tactic_bvNormalize);
l_Lean_Parser_bv__normalize = _init_l_Lean_Parser_bv__normalize();
lean_mark_persistent(l_Lean_Parser_bv__normalize);
l_Lean_Parser_bvNormalizeProcBuiltinAttr = _init_l_Lean_Parser_bvNormalizeProcBuiltinAttr();
lean_mark_persistent(l_Lean_Parser_bvNormalizeProcBuiltinAttr);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
