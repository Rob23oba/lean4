// Lean compiler output
// Module: Init.Grind.Propagator
// Imports: Init.NotationExtra
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
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_grindPropagatorBuiltinAttr;
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d__;
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
extern lean_object* l_Lean_Parser_Tactic_simpPre;
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_simpPost;
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d__;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d__() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("command_Grind_propagator___(_):=_", 33, 33);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
x_5 = lean_unsigned_to_nat(1022u);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("optional", 8, 8);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("docComment", 10, 10);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_mk_string_unchecked("grind_propagator ", 17, 17);
x_15 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_inc(x_7);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_mk_string_unchecked("orelse", 6, 6);
x_18 = l_Lean_Name_mkStr1(x_17);
x_19 = l_Lean_Parser_Tactic_simpPre;
x_20 = l_Lean_Parser_Tactic_simpPost;
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_20);
lean_inc(x_7);
x_22 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_22, 0, x_7);
lean_ctor_set(x_22, 1, x_16);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_mk_string_unchecked("ident", 5, 5);
x_24 = l_Lean_Name_mkStr1(x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_inc(x_25);
lean_inc(x_7);
x_26 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_22);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_mk_string_unchecked(" (", 2, 2);
x_28 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_inc(x_7);
x_29 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_29, 0, x_7);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_29, 2, x_28);
lean_inc(x_7);
x_30 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_30, 0, x_7);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_30, 2, x_25);
x_31 = lean_mk_string_unchecked(")", 1, 1);
x_32 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_inc(x_7);
x_33 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_33, 0, x_7);
lean_ctor_set(x_33, 1, x_30);
lean_ctor_set(x_33, 2, x_32);
x_34 = lean_mk_string_unchecked(" := ", 4, 4);
x_35 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_inc(x_7);
x_36 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_36, 0, x_7);
lean_ctor_set(x_36, 1, x_33);
lean_ctor_set(x_36, 2, x_35);
x_37 = lean_mk_string_unchecked("term", 4, 4);
x_38 = l_Lean_Name_mkStr1(x_37);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_41, 0, x_7);
lean_ctor_set(x_41, 1, x_36);
lean_ctor_set(x_41, 2, x_40);
x_42 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_42, 0, x_4);
lean_ctor_set(x_42, 1, x_5);
lean_ctor_set(x_42, 2, x_41);
return x_42;
}
}
static lean_object* _init_l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d__() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("command_Builtin_grind_propagator____:=_", 39, 39);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
x_5 = lean_unsigned_to_nat(1022u);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("optional", 8, 8);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("docComment", 10, 10);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_mk_string_unchecked("builtin_grind_propagator ", 25, 25);
x_15 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_inc(x_7);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_mk_string_unchecked("ident", 5, 5);
x_18 = l_Lean_Name_mkStr1(x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_19);
lean_inc(x_7);
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_mk_string_unchecked("orelse", 6, 6);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = l_Lean_Parser_Tactic_simpPre;
x_24 = l_Lean_Parser_Tactic_simpPost;
x_25 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_24);
lean_inc(x_7);
x_26 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_20);
lean_ctor_set(x_26, 2, x_25);
lean_inc(x_7);
x_27 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_27, 0, x_7);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_19);
x_28 = lean_mk_string_unchecked(" := ", 4, 4);
x_29 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_29, 0, x_28);
lean_inc(x_7);
x_30 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_30, 0, x_7);
lean_ctor_set(x_30, 1, x_27);
lean_ctor_set(x_30, 2, x_29);
x_31 = lean_mk_string_unchecked("term", 4, 4);
x_32 = l_Lean_Name_mkStr1(x_31);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_35, 0, x_7);
lean_ctor_set(x_35, 1, x_30);
lean_ctor_set(x_35, 2, x_34);
x_36 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_36, 0, x_4);
lean_ctor_set(x_36, 1, x_5);
lean_ctor_set(x_36, 2, x_35);
return x_36;
}
}
static lean_object* _init_l_Lean_Parser_grindPropagatorBuiltinAttr() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("grindPropagatorBuiltinAttr", 26, 26);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
x_5 = lean_unsigned_to_nat(1022u);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("builtin_grind_propagator", 24, 24);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_10, 0, x_8);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_11);
x_12 = lean_mk_string_unchecked("orelse", 6, 6);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = l_Lean_Parser_Tactic_simpPre;
x_15 = l_Lean_Parser_Tactic_simpPost;
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
lean_inc(x_7);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_10);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_mk_string_unchecked("ident", 5, 5);
x_19 = l_Lean_Name_mkStr1(x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_5);
lean_ctor_set(x_22, 2, x_21);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_115 = lean_mk_string_unchecked("command_Builtin_grind_propagator____:=_", 39, 39);
lean_inc(x_5);
lean_inc(x_4);
x_116 = l_Lean_Name_mkStr3(x_4, x_5, x_115);
lean_inc(x_1);
x_117 = l_Lean_Syntax_isOfKind(x_1, x_116);
lean_dec(x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_118 = lean_box(1);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_3);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_120 = lean_unsigned_to_nat(0u);
x_121 = l_Lean_Syntax_getArg(x_1, x_120);
x_122 = l_Lean_Syntax_isNone(x_121);
if (x_122 == 0)
{
lean_object* x_123; uint8_t x_124; 
x_123 = lean_unsigned_to_nat(1u);
lean_inc(x_121);
x_124 = l_Lean_Syntax_matchesNull(x_121, x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; 
lean_dec(x_121);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_125 = lean_box(1);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_3);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_127 = l_Lean_Syntax_getArg(x_121, x_120);
lean_dec(x_121);
x_128 = lean_mk_string_unchecked("Command", 7, 7);
x_129 = lean_mk_string_unchecked("docComment", 10, 10);
lean_inc(x_5);
lean_inc(x_4);
x_130 = l_Lean_Name_mkStr4(x_4, x_5, x_128, x_129);
lean_inc(x_127);
x_131 = l_Lean_Syntax_isOfKind(x_127, x_130);
lean_dec(x_130);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; 
lean_dec(x_127);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_132 = lean_box(1);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_3);
return x_133;
}
else
{
lean_object* x_134; 
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_127);
x_76 = x_134;
x_77 = x_2;
x_78 = x_3;
goto block_114;
}
}
}
else
{
lean_object* x_135; 
lean_dec(x_121);
x_135 = lean_box(0);
x_76 = x_135;
x_77 = x_2;
x_78 = x_3;
goto block_114;
}
}
block_75:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_inc(x_10);
x_19 = l_Array_append(lean_box(0), x_10, x_18);
lean_dec(x_18);
lean_inc(x_12);
lean_inc(x_13);
x_20 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_12);
lean_ctor_set(x_20, 2, x_19);
lean_inc(x_12);
lean_inc(x_13);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_12);
lean_ctor_set(x_21, 2, x_10);
lean_inc_n(x_21, 5);
lean_inc(x_13);
x_22 = l_Lean_Syntax_node6(x_13, x_9, x_20, x_21, x_21, x_21, x_21, x_21);
x_23 = lean_mk_string_unchecked("definition", 10, 10);
lean_inc(x_11);
lean_inc(x_5);
lean_inc(x_4);
x_24 = l_Lean_Name_mkStr4(x_4, x_5, x_11, x_23);
x_25 = lean_mk_string_unchecked("def", 3, 3);
lean_inc(x_13);
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_13);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_mk_string_unchecked("declId", 6, 6);
lean_inc(x_11);
lean_inc(x_5);
lean_inc(x_4);
x_28 = l_Lean_Name_mkStr4(x_4, x_5, x_11, x_27);
lean_inc(x_21);
lean_inc(x_8);
lean_inc(x_13);
x_29 = l_Lean_Syntax_node2(x_13, x_28, x_8, x_21);
x_30 = lean_mk_string_unchecked("optDeclSig", 10, 10);
lean_inc(x_11);
lean_inc(x_5);
lean_inc(x_4);
x_31 = l_Lean_Name_mkStr4(x_4, x_5, x_11, x_30);
x_32 = lean_mk_string_unchecked("Term", 4, 4);
x_33 = lean_mk_string_unchecked("typeSpec", 8, 8);
lean_inc(x_32);
lean_inc(x_5);
lean_inc(x_4);
x_34 = l_Lean_Name_mkStr4(x_4, x_5, x_32, x_33);
x_35 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_13);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_13);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_mk_syntax_ident(x_16);
lean_inc(x_13);
x_38 = l_Lean_Syntax_node2(x_13, x_34, x_36, x_37);
lean_inc(x_12);
lean_inc(x_13);
x_39 = l_Lean_Syntax_node1(x_13, x_12, x_38);
lean_inc(x_21);
lean_inc(x_13);
x_40 = l_Lean_Syntax_node2(x_13, x_31, x_21, x_39);
x_41 = lean_mk_string_unchecked("declValSimple", 13, 13);
lean_inc(x_11);
lean_inc(x_5);
lean_inc(x_4);
x_42 = l_Lean_Name_mkStr4(x_4, x_5, x_11, x_41);
x_43 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_13);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_13);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_mk_string_unchecked("Termination", 11, 11);
x_46 = lean_mk_string_unchecked("suffix", 6, 6);
lean_inc(x_5);
lean_inc(x_4);
x_47 = l_Lean_Name_mkStr4(x_4, x_5, x_45, x_46);
lean_inc_n(x_21, 2);
lean_inc(x_13);
x_48 = l_Lean_Syntax_node2(x_13, x_47, x_21, x_21);
lean_inc(x_21);
lean_inc(x_13);
x_49 = l_Lean_Syntax_node4(x_13, x_42, x_44, x_15, x_48, x_21);
lean_inc(x_21);
lean_inc(x_13);
x_50 = l_Lean_Syntax_node5(x_13, x_24, x_26, x_29, x_40, x_49, x_21);
lean_inc(x_13);
x_51 = l_Lean_Syntax_node2(x_13, x_17, x_22, x_50);
x_52 = lean_mk_string_unchecked("attribute", 9, 9);
lean_inc(x_52);
lean_inc(x_5);
lean_inc(x_4);
x_53 = l_Lean_Name_mkStr4(x_4, x_5, x_11, x_52);
lean_inc(x_13);
x_54 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_54, 0, x_13);
lean_ctor_set(x_54, 1, x_52);
x_55 = lean_mk_string_unchecked("[", 1, 1);
lean_inc(x_13);
x_56 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_56, 0, x_13);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_mk_string_unchecked("attrInstance", 12, 12);
lean_inc(x_32);
lean_inc(x_5);
lean_inc(x_4);
x_58 = l_Lean_Name_mkStr4(x_4, x_5, x_32, x_57);
x_59 = lean_mk_string_unchecked("attrKind", 8, 8);
lean_inc(x_5);
lean_inc(x_4);
x_60 = l_Lean_Name_mkStr4(x_4, x_5, x_32, x_59);
lean_inc(x_13);
x_61 = l_Lean_Syntax_node1(x_13, x_60, x_21);
x_62 = lean_mk_string_unchecked("grindPropagatorBuiltinAttr", 26, 26);
x_63 = l_Lean_Name_mkStr3(x_4, x_5, x_62);
x_64 = lean_mk_string_unchecked("builtin_grind_propagator", 24, 24);
lean_inc(x_13);
x_65 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_65, 0, x_13);
lean_ctor_set(x_65, 1, x_64);
lean_inc(x_13);
x_66 = l_Lean_Syntax_node3(x_13, x_63, x_65, x_7, x_6);
lean_inc(x_13);
x_67 = l_Lean_Syntax_node2(x_13, x_58, x_61, x_66);
lean_inc(x_12);
lean_inc(x_13);
x_68 = l_Lean_Syntax_node1(x_13, x_12, x_67);
x_69 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_13);
x_70 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_70, 0, x_13);
lean_ctor_set(x_70, 1, x_69);
lean_inc(x_12);
lean_inc(x_13);
x_71 = l_Lean_Syntax_node1(x_13, x_12, x_8);
lean_inc(x_13);
x_72 = l_Lean_Syntax_node5(x_13, x_53, x_54, x_56, x_68, x_70, x_71);
x_73 = l_Lean_Syntax_node2(x_13, x_12, x_51, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_14);
return x_74;
}
block_114:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_79 = lean_unsigned_to_nat(2u);
x_80 = l_Lean_Syntax_getArg(x_1, x_79);
x_81 = lean_mk_string_unchecked("ident", 5, 5);
x_82 = l_Lean_Name_mkStr1(x_81);
lean_inc(x_80);
x_83 = l_Lean_Syntax_isOfKind(x_80, x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_76);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_84 = lean_box(1);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_78);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = lean_unsigned_to_nat(4u);
x_87 = l_Lean_Syntax_getArg(x_1, x_86);
lean_inc(x_87);
x_88 = l_Lean_Syntax_isOfKind(x_87, x_82);
lean_dec(x_82);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_87);
lean_dec(x_80);
lean_dec(x_76);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_89 = lean_box(1);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_78);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_91 = lean_unsigned_to_nat(3u);
x_92 = l_Lean_Syntax_getArg(x_1, x_91);
x_93 = lean_unsigned_to_nat(6u);
x_94 = l_Lean_Syntax_getArg(x_1, x_93);
lean_dec(x_1);
x_95 = lean_mk_string_unchecked("Meta", 4, 4);
x_96 = lean_mk_string_unchecked("Grind", 5, 5);
x_97 = lean_mk_string_unchecked("Propagator", 10, 10);
lean_inc(x_4);
x_98 = l_Lean_Name_mkStr4(x_4, x_95, x_96, x_97);
x_99 = lean_ctor_get(x_77, 5);
x_100 = lean_box(0);
x_101 = lean_unbox(x_100);
x_102 = l_Lean_SourceInfo_fromRef(x_99, x_101);
x_103 = lean_mk_string_unchecked("null", 4, 4);
x_104 = l_Lean_Name_mkStr1(x_103);
x_105 = lean_mk_string_unchecked("Command", 7, 7);
x_106 = lean_mk_string_unchecked("declaration", 11, 11);
lean_inc(x_105);
lean_inc(x_5);
lean_inc(x_4);
x_107 = l_Lean_Name_mkStr4(x_4, x_5, x_105, x_106);
x_108 = lean_mk_string_unchecked("declModifiers", 13, 13);
lean_inc(x_105);
lean_inc(x_5);
lean_inc(x_4);
x_109 = l_Lean_Name_mkStr4(x_4, x_5, x_105, x_108);
x_110 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_111; 
x_111 = l_Array_empty(lean_box(0));
x_6 = x_87;
x_7 = x_92;
x_8 = x_80;
x_9 = x_109;
x_10 = x_110;
x_11 = x_105;
x_12 = x_104;
x_13 = x_102;
x_14 = x_78;
x_15 = x_94;
x_16 = x_98;
x_17 = x_107;
x_18 = x_111;
goto block_75;
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_76, 0);
lean_inc(x_112);
lean_dec(x_76);
x_113 = l_Array_mkArray1___redArg(x_112);
x_6 = x_87;
x_7 = x_92;
x_8 = x_80;
x_9 = x_109;
x_10 = x_110;
x_11 = x_105;
x_12 = x_104;
x_13 = x_102;
x_14 = x_78;
x_15 = x_94;
x_16 = x_98;
x_17 = x_107;
x_18 = x_113;
goto block_75;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser___aux__Init__Grind__Propagator______macroRules__Lean__Parser__command__Builtin__grind__propagator_________x3a_x3d____1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init_NotationExtra(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_Propagator(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_NotationExtra(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d__ = _init_l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d__();
lean_mark_persistent(l_Lean_Parser_command__Grind__propagator_______x28___x29_x3a_x3d__);
l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d__ = _init_l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d__();
lean_mark_persistent(l_Lean_Parser_command__Builtin__grind__propagator_________x3a_x3d__);
l_Lean_Parser_grindPropagatorBuiltinAttr = _init_l_Lean_Parser_grindPropagatorBuiltinAttr();
lean_mark_persistent(l_Lean_Parser_grindPropagatorBuiltinAttr);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
