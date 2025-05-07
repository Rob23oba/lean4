// Lean compiler output
// Module: Lean.Elab.Tactic.Match
// Imports: Lean.Parser.Term Lean.Elab.Match Lean.Elab.Tactic.Basic Lean.Elab.Tactic.Induction
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_withMacroExpansionInfo___at___Lean_Elab_Tactic_adaptExpander_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__1(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_Tactic_getMainTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalMatch__1(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalMatch___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalMatch___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setKind(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 5);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_unsigned_to_nat(5u);
x_12 = l_Lean_Syntax_getArg(x_3, x_11);
x_13 = lean_usize_dec_lt(x_7, x_6);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_15 = lean_unsigned_to_nat(1u);
x_28 = lean_mk_string_unchecked("Lean", 4, 4);
x_29 = lean_mk_string_unchecked("Parser", 6, 6);
x_30 = lean_mk_string_unchecked("Term", 4, 4);
x_31 = lean_array_uget(x_5, x_7);
x_32 = lean_ctor_get(x_8, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_8, 1);
lean_inc(x_33);
lean_dec(x_8);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_mk_empty_array_with_capacity(x_15);
x_37 = lean_array_push(x_36, x_31);
x_38 = lean_mk_string_unchecked("null", 4, 4);
x_39 = l_Lean_Name_mkStr1(x_38);
x_40 = lean_box(2);
lean_inc(x_39);
x_41 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
lean_ctor_set(x_41, 2, x_37);
lean_inc(x_1);
x_42 = l_Lean_Syntax_setArg(x_1, x_15, x_41);
x_43 = lean_mk_string_unchecked("syntheticHole", 13, 13);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
x_44 = l_Lean_Name_mkStr4(x_28, x_29, x_30, x_43);
lean_inc(x_2);
x_45 = l_Lean_Syntax_isOfKind(x_2, x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_unsigned_to_nat(3u);
x_58 = lean_mk_string_unchecked("hole", 4, 4);
lean_inc(x_29);
lean_inc(x_28);
x_59 = l_Lean_Name_mkStr4(x_28, x_29, x_30, x_58);
lean_inc(x_2);
x_60 = l_Lean_Syntax_isOfKind(x_2, x_59);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
lean_dec(x_12);
x_61 = lean_ctor_get(x_10, 0);
lean_inc(x_61);
x_62 = lean_nat_add(x_61, x_15);
x_63 = lean_ctor_get(x_10, 1);
lean_inc(x_63);
lean_dec(x_10);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_ctor_get(x_9, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_9, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_9, 3);
lean_inc(x_67);
x_68 = lean_ctor_get(x_9, 4);
lean_inc(x_68);
x_69 = lean_ctor_get(x_9, 5);
lean_inc(x_69);
lean_inc(x_61);
lean_inc(x_66);
x_70 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_70, 0, x_65);
lean_ctor_set(x_70, 1, x_66);
lean_ctor_set(x_70, 2, x_61);
lean_ctor_set(x_70, 3, x_67);
lean_ctor_set(x_70, 4, x_68);
lean_ctor_set(x_70, 5, x_69);
x_71 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___lam__0(x_70, x_70, x_64);
lean_dec(x_70);
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = lean_ctor_get(x_71, 1);
x_75 = lean_mk_string_unchecked("rhs", 3, 3);
lean_inc(x_75);
x_76 = l_Lean_Name_mkStr1(x_75);
x_77 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___lam__0(x_9, x_9, x_74);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_79 = lean_ctor_get(x_77, 0);
x_80 = lean_ctor_get(x_77, 1);
x_81 = lean_mk_string_unchecked("\?", 1, 1);
x_82 = l_String_toSubstring_x27(x_75);
x_83 = l_Lean_addMacroScope(x_66, x_76, x_61);
x_84 = lean_box(0);
x_85 = l_Lean_SourceInfo_fromRef(x_73, x_60);
lean_dec(x_73);
lean_inc(x_85);
lean_ctor_set_tag(x_77, 2);
lean_ctor_set(x_77, 1, x_81);
lean_ctor_set(x_77, 0, x_85);
lean_inc(x_85);
x_86 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_82);
lean_ctor_set(x_86, 2, x_83);
lean_ctor_set(x_86, 3, x_84);
x_87 = l_Lean_Syntax_node2(x_85, x_44, x_77, x_86);
x_88 = l_Lean_Syntax_getArg(x_87, x_15);
x_89 = l_Lean_SourceInfo_fromRef(x_79, x_60);
lean_dec(x_79);
x_90 = lean_mk_string_unchecked("Tactic", 6, 6);
x_91 = lean_mk_string_unchecked("case", 4, 4);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_29);
lean_inc(x_28);
x_92 = l_Lean_Name_mkStr4(x_28, x_29, x_90, x_91);
lean_inc(x_89);
lean_ctor_set_tag(x_71, 2);
lean_ctor_set(x_71, 1, x_91);
lean_ctor_set(x_71, 0, x_89);
x_93 = lean_mk_string_unchecked("caseArg", 7, 7);
lean_inc(x_90);
lean_inc(x_29);
lean_inc(x_28);
x_94 = l_Lean_Name_mkStr4(x_28, x_29, x_90, x_93);
x_95 = lean_mk_string_unchecked("binderIdent", 11, 11);
lean_inc(x_28);
x_96 = l_Lean_Name_mkStr2(x_28, x_95);
lean_inc(x_89);
x_97 = l_Lean_Syntax_node1(x_89, x_96, x_88);
x_98 = l_Array_mkArray0(lean_box(0));
lean_inc(x_39);
lean_inc(x_89);
x_99 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_99, 0, x_89);
lean_ctor_set(x_99, 1, x_39);
lean_ctor_set(x_99, 2, x_98);
lean_inc(x_99);
lean_inc(x_89);
x_100 = l_Lean_Syntax_node2(x_89, x_94, x_97, x_99);
lean_inc(x_39);
lean_inc(x_89);
x_101 = l_Lean_Syntax_node1(x_89, x_39, x_100);
x_102 = lean_unsigned_to_nat(2u);
x_103 = l_Lean_Syntax_getArg(x_42, x_102);
x_104 = l_Lean_SourceInfo_fromRef(x_103, x_13);
x_105 = lean_mk_string_unchecked("=>", 2, 2);
x_106 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_90);
lean_inc(x_29);
lean_inc(x_28);
x_108 = l_Lean_Name_mkStr4(x_28, x_29, x_90, x_107);
x_109 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_90);
lean_inc(x_29);
lean_inc(x_28);
x_110 = l_Lean_Name_mkStr4(x_28, x_29, x_90, x_109);
x_111 = lean_mk_string_unchecked("withAnnotateState", 17, 17);
lean_inc(x_90);
lean_inc(x_29);
lean_inc(x_28);
x_112 = l_Lean_Name_mkStr4(x_28, x_29, x_90, x_111);
x_113 = lean_mk_string_unchecked("with_annotate_state", 19, 19);
lean_inc(x_89);
x_114 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_114, 0, x_89);
lean_ctor_set(x_114, 1, x_113);
x_115 = l_Lean_Syntax_getArg(x_42, x_46);
x_116 = lean_mk_empty_array_with_capacity(x_102);
x_117 = lean_array_push(x_116, x_115);
x_118 = lean_array_push(x_117, x_103);
lean_inc(x_39);
x_119 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_119, 0, x_40);
lean_ctor_set(x_119, 1, x_39);
lean_ctor_set(x_119, 2, x_118);
x_120 = lean_mk_string_unchecked("skip", 4, 4);
lean_inc(x_120);
x_121 = l_Lean_Name_mkStr4(x_28, x_29, x_90, x_120);
lean_inc(x_89);
x_122 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_122, 0, x_89);
lean_ctor_set(x_122, 1, x_120);
lean_inc(x_89);
x_123 = l_Lean_Syntax_node1(x_89, x_121, x_122);
lean_inc(x_89);
x_124 = l_Lean_Syntax_node3(x_89, x_112, x_114, x_119, x_123);
lean_inc(x_2);
lean_inc(x_89);
x_125 = l_Lean_Syntax_node3(x_89, x_39, x_124, x_99, x_2);
lean_inc(x_89);
x_126 = l_Lean_Syntax_node1(x_89, x_110, x_125);
lean_inc(x_89);
x_127 = l_Lean_Syntax_node1(x_89, x_108, x_126);
x_128 = l_Lean_Syntax_node4(x_89, x_92, x_71, x_101, x_106, x_127);
x_129 = lean_array_push(x_34, x_128);
x_130 = l_Lean_Syntax_setArg(x_42, x_47, x_87);
x_16 = x_130;
x_17 = x_32;
x_18 = x_129;
x_19 = x_35;
x_20 = x_80;
goto block_27;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_131 = lean_ctor_get(x_77, 0);
x_132 = lean_ctor_get(x_77, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_77);
x_133 = lean_mk_string_unchecked("\?", 1, 1);
x_134 = l_String_toSubstring_x27(x_75);
x_135 = l_Lean_addMacroScope(x_66, x_76, x_61);
x_136 = lean_box(0);
x_137 = l_Lean_SourceInfo_fromRef(x_73, x_60);
lean_dec(x_73);
lean_inc(x_137);
x_138 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_133);
lean_inc(x_137);
x_139 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_134);
lean_ctor_set(x_139, 2, x_135);
lean_ctor_set(x_139, 3, x_136);
x_140 = l_Lean_Syntax_node2(x_137, x_44, x_138, x_139);
x_141 = l_Lean_Syntax_getArg(x_140, x_15);
x_142 = l_Lean_SourceInfo_fromRef(x_131, x_60);
lean_dec(x_131);
x_143 = lean_mk_string_unchecked("Tactic", 6, 6);
x_144 = lean_mk_string_unchecked("case", 4, 4);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_29);
lean_inc(x_28);
x_145 = l_Lean_Name_mkStr4(x_28, x_29, x_143, x_144);
lean_inc(x_142);
lean_ctor_set_tag(x_71, 2);
lean_ctor_set(x_71, 1, x_144);
lean_ctor_set(x_71, 0, x_142);
x_146 = lean_mk_string_unchecked("caseArg", 7, 7);
lean_inc(x_143);
lean_inc(x_29);
lean_inc(x_28);
x_147 = l_Lean_Name_mkStr4(x_28, x_29, x_143, x_146);
x_148 = lean_mk_string_unchecked("binderIdent", 11, 11);
lean_inc(x_28);
x_149 = l_Lean_Name_mkStr2(x_28, x_148);
lean_inc(x_142);
x_150 = l_Lean_Syntax_node1(x_142, x_149, x_141);
x_151 = l_Array_mkArray0(lean_box(0));
lean_inc(x_39);
lean_inc(x_142);
x_152 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_152, 0, x_142);
lean_ctor_set(x_152, 1, x_39);
lean_ctor_set(x_152, 2, x_151);
lean_inc(x_152);
lean_inc(x_142);
x_153 = l_Lean_Syntax_node2(x_142, x_147, x_150, x_152);
lean_inc(x_39);
lean_inc(x_142);
x_154 = l_Lean_Syntax_node1(x_142, x_39, x_153);
x_155 = lean_unsigned_to_nat(2u);
x_156 = l_Lean_Syntax_getArg(x_42, x_155);
x_157 = l_Lean_SourceInfo_fromRef(x_156, x_13);
x_158 = lean_mk_string_unchecked("=>", 2, 2);
x_159 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
x_160 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_143);
lean_inc(x_29);
lean_inc(x_28);
x_161 = l_Lean_Name_mkStr4(x_28, x_29, x_143, x_160);
x_162 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_143);
lean_inc(x_29);
lean_inc(x_28);
x_163 = l_Lean_Name_mkStr4(x_28, x_29, x_143, x_162);
x_164 = lean_mk_string_unchecked("withAnnotateState", 17, 17);
lean_inc(x_143);
lean_inc(x_29);
lean_inc(x_28);
x_165 = l_Lean_Name_mkStr4(x_28, x_29, x_143, x_164);
x_166 = lean_mk_string_unchecked("with_annotate_state", 19, 19);
lean_inc(x_142);
x_167 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_167, 0, x_142);
lean_ctor_set(x_167, 1, x_166);
x_168 = l_Lean_Syntax_getArg(x_42, x_46);
x_169 = lean_mk_empty_array_with_capacity(x_155);
x_170 = lean_array_push(x_169, x_168);
x_171 = lean_array_push(x_170, x_156);
lean_inc(x_39);
x_172 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_172, 0, x_40);
lean_ctor_set(x_172, 1, x_39);
lean_ctor_set(x_172, 2, x_171);
x_173 = lean_mk_string_unchecked("skip", 4, 4);
lean_inc(x_173);
x_174 = l_Lean_Name_mkStr4(x_28, x_29, x_143, x_173);
lean_inc(x_142);
x_175 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_175, 0, x_142);
lean_ctor_set(x_175, 1, x_173);
lean_inc(x_142);
x_176 = l_Lean_Syntax_node1(x_142, x_174, x_175);
lean_inc(x_142);
x_177 = l_Lean_Syntax_node3(x_142, x_165, x_167, x_172, x_176);
lean_inc(x_2);
lean_inc(x_142);
x_178 = l_Lean_Syntax_node3(x_142, x_39, x_177, x_152, x_2);
lean_inc(x_142);
x_179 = l_Lean_Syntax_node1(x_142, x_163, x_178);
lean_inc(x_142);
x_180 = l_Lean_Syntax_node1(x_142, x_161, x_179);
x_181 = l_Lean_Syntax_node4(x_142, x_145, x_71, x_154, x_159, x_180);
x_182 = lean_array_push(x_34, x_181);
x_183 = l_Lean_Syntax_setArg(x_42, x_47, x_140);
x_16 = x_183;
x_17 = x_32;
x_18 = x_182;
x_19 = x_35;
x_20 = x_132;
goto block_27;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_184 = lean_ctor_get(x_71, 0);
x_185 = lean_ctor_get(x_71, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_71);
x_186 = lean_mk_string_unchecked("rhs", 3, 3);
lean_inc(x_186);
x_187 = l_Lean_Name_mkStr1(x_186);
x_188 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___lam__0(x_9, x_9, x_185);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_191 = x_188;
} else {
 lean_dec_ref(x_188);
 x_191 = lean_box(0);
}
x_192 = lean_mk_string_unchecked("\?", 1, 1);
x_193 = l_String_toSubstring_x27(x_186);
x_194 = l_Lean_addMacroScope(x_66, x_187, x_61);
x_195 = lean_box(0);
x_196 = l_Lean_SourceInfo_fromRef(x_184, x_60);
lean_dec(x_184);
lean_inc(x_196);
if (lean_is_scalar(x_191)) {
 x_197 = lean_alloc_ctor(2, 2, 0);
} else {
 x_197 = x_191;
 lean_ctor_set_tag(x_197, 2);
}
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_192);
lean_inc(x_196);
x_198 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_193);
lean_ctor_set(x_198, 2, x_194);
lean_ctor_set(x_198, 3, x_195);
x_199 = l_Lean_Syntax_node2(x_196, x_44, x_197, x_198);
x_200 = l_Lean_Syntax_getArg(x_199, x_15);
x_201 = l_Lean_SourceInfo_fromRef(x_189, x_60);
lean_dec(x_189);
x_202 = lean_mk_string_unchecked("Tactic", 6, 6);
x_203 = lean_mk_string_unchecked("case", 4, 4);
lean_inc(x_203);
lean_inc(x_202);
lean_inc(x_29);
lean_inc(x_28);
x_204 = l_Lean_Name_mkStr4(x_28, x_29, x_202, x_203);
lean_inc(x_201);
x_205 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_205, 0, x_201);
lean_ctor_set(x_205, 1, x_203);
x_206 = lean_mk_string_unchecked("caseArg", 7, 7);
lean_inc(x_202);
lean_inc(x_29);
lean_inc(x_28);
x_207 = l_Lean_Name_mkStr4(x_28, x_29, x_202, x_206);
x_208 = lean_mk_string_unchecked("binderIdent", 11, 11);
lean_inc(x_28);
x_209 = l_Lean_Name_mkStr2(x_28, x_208);
lean_inc(x_201);
x_210 = l_Lean_Syntax_node1(x_201, x_209, x_200);
x_211 = l_Array_mkArray0(lean_box(0));
lean_inc(x_39);
lean_inc(x_201);
x_212 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_212, 0, x_201);
lean_ctor_set(x_212, 1, x_39);
lean_ctor_set(x_212, 2, x_211);
lean_inc(x_212);
lean_inc(x_201);
x_213 = l_Lean_Syntax_node2(x_201, x_207, x_210, x_212);
lean_inc(x_39);
lean_inc(x_201);
x_214 = l_Lean_Syntax_node1(x_201, x_39, x_213);
x_215 = lean_unsigned_to_nat(2u);
x_216 = l_Lean_Syntax_getArg(x_42, x_215);
x_217 = l_Lean_SourceInfo_fromRef(x_216, x_13);
x_218 = lean_mk_string_unchecked("=>", 2, 2);
x_219 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
x_220 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_202);
lean_inc(x_29);
lean_inc(x_28);
x_221 = l_Lean_Name_mkStr4(x_28, x_29, x_202, x_220);
x_222 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_202);
lean_inc(x_29);
lean_inc(x_28);
x_223 = l_Lean_Name_mkStr4(x_28, x_29, x_202, x_222);
x_224 = lean_mk_string_unchecked("withAnnotateState", 17, 17);
lean_inc(x_202);
lean_inc(x_29);
lean_inc(x_28);
x_225 = l_Lean_Name_mkStr4(x_28, x_29, x_202, x_224);
x_226 = lean_mk_string_unchecked("with_annotate_state", 19, 19);
lean_inc(x_201);
x_227 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_227, 0, x_201);
lean_ctor_set(x_227, 1, x_226);
x_228 = l_Lean_Syntax_getArg(x_42, x_46);
x_229 = lean_mk_empty_array_with_capacity(x_215);
x_230 = lean_array_push(x_229, x_228);
x_231 = lean_array_push(x_230, x_216);
lean_inc(x_39);
x_232 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_232, 0, x_40);
lean_ctor_set(x_232, 1, x_39);
lean_ctor_set(x_232, 2, x_231);
x_233 = lean_mk_string_unchecked("skip", 4, 4);
lean_inc(x_233);
x_234 = l_Lean_Name_mkStr4(x_28, x_29, x_202, x_233);
lean_inc(x_201);
x_235 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_235, 0, x_201);
lean_ctor_set(x_235, 1, x_233);
lean_inc(x_201);
x_236 = l_Lean_Syntax_node1(x_201, x_234, x_235);
lean_inc(x_201);
x_237 = l_Lean_Syntax_node3(x_201, x_225, x_227, x_232, x_236);
lean_inc(x_2);
lean_inc(x_201);
x_238 = l_Lean_Syntax_node3(x_201, x_39, x_237, x_212, x_2);
lean_inc(x_201);
x_239 = l_Lean_Syntax_node1(x_201, x_223, x_238);
lean_inc(x_201);
x_240 = l_Lean_Syntax_node1(x_201, x_221, x_239);
x_241 = l_Lean_Syntax_node4(x_201, x_204, x_205, x_214, x_219, x_240);
x_242 = lean_array_push(x_34, x_241);
x_243 = l_Lean_Syntax_setArg(x_42, x_47, x_199);
x_16 = x_243;
x_17 = x_32;
x_18 = x_242;
x_19 = x_35;
x_20 = x_190;
goto block_27;
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; 
lean_dec(x_39);
lean_dec(x_29);
lean_dec(x_28);
x_244 = l_Lean_Syntax_getArg(x_12, x_46);
lean_dec(x_12);
x_245 = l_Lean_Syntax_getArgs(x_244);
lean_dec(x_244);
x_246 = lean_array_get_size(x_245);
lean_dec(x_245);
x_247 = lean_nat_dec_lt(x_15, x_246);
lean_dec(x_246);
if (x_247 == 0)
{
lean_inc(x_4);
x_48 = x_4;
goto block_57;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_248 = lean_mk_string_unchecked("match", 5, 5);
x_249 = l_Lean_Name_mkStr1(x_248);
lean_inc(x_35);
x_250 = lean_name_append_index_after(x_249, x_35);
lean_inc(x_4);
x_251 = l_Lean_Name_append(x_4, x_250);
x_48 = x_251;
goto block_57;
}
}
block_57:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_49 = lean_ctor_get(x_9, 5);
lean_inc(x_49);
x_50 = l_Lean_SourceInfo_fromRef(x_49, x_45);
lean_dec(x_49);
x_51 = lean_mk_string_unchecked("\?", 1, 1);
lean_inc(x_50);
x_52 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_mkIdentFrom(x_2, x_48, x_45);
x_54 = l_Lean_Syntax_node2(x_50, x_44, x_52, x_53);
x_55 = lean_nat_add(x_35, x_15);
lean_dec(x_35);
x_56 = l_Lean_Syntax_setArg(x_42, x_47, x_54);
x_16 = x_56;
x_17 = x_32;
x_18 = x_34;
x_19 = x_55;
x_20 = x_10;
goto block_27;
}
}
else
{
lean_dec(x_44);
lean_dec(x_39);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_12);
x_16 = x_42;
x_17 = x_32;
x_18 = x_34;
x_19 = x_35;
x_20 = x_10;
goto block_27;
}
block_27:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
x_21 = lean_array_push(x_17, x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_usize_of_nat(x_15);
x_25 = lean_usize_add(x_7, x_24);
x_7 = x_25;
x_8 = x_23;
x_10 = x_20;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_5, x_4);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; lean_object* x_30; size_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_array_uget(x_3, x_5);
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_mk_string_unchecked("Lean", 4, 4);
x_18 = lean_mk_string_unchecked("Parser", 6, 6);
x_19 = lean_mk_string_unchecked("Term", 4, 4);
x_20 = lean_mk_string_unchecked("matchAlt", 8, 8);
x_21 = l_Lean_Name_mkStr4(x_17, x_18, x_19, x_20);
x_22 = l_Lean_Syntax_setKind(x_12, x_21);
x_23 = lean_unsigned_to_nat(3u);
x_24 = l_Lean_Syntax_getArg(x_22, x_23);
x_25 = l_Lean_Syntax_getArg(x_22, x_11);
x_26 = l_Lean_Syntax_getSepArgs(x_25);
lean_dec(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_27, 1, x_16);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_13);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_array_size(x_26);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_usize_of_nat(x_30);
lean_inc(x_7);
lean_inc(x_2);
x_32 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0(x_22, x_24, x_1, x_2, x_26, x_29, x_31, x_28, x_7, x_8);
lean_dec(x_26);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_usize_of_nat(x_11);
x_36 = lean_usize_add(x_5, x_35);
x_5 = x_36;
x_6 = x_33;
x_8 = x_34;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_5, x_4);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; lean_object* x_30; size_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; lean_object* x_37; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_array_uget(x_3, x_5);
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_mk_string_unchecked("Lean", 4, 4);
x_18 = lean_mk_string_unchecked("Parser", 6, 6);
x_19 = lean_mk_string_unchecked("Term", 4, 4);
x_20 = lean_mk_string_unchecked("matchAlt", 8, 8);
x_21 = l_Lean_Name_mkStr4(x_17, x_18, x_19, x_20);
x_22 = l_Lean_Syntax_setKind(x_12, x_21);
x_23 = lean_unsigned_to_nat(3u);
x_24 = l_Lean_Syntax_getArg(x_22, x_23);
x_25 = l_Lean_Syntax_getArg(x_22, x_11);
x_26 = l_Lean_Syntax_getSepArgs(x_25);
lean_dec(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_27, 1, x_16);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_13);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_array_size(x_26);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_usize_of_nat(x_30);
lean_inc(x_7);
lean_inc(x_2);
x_32 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0(x_22, x_24, x_1, x_2, x_26, x_29, x_31, x_28, x_7, x_8);
lean_dec(x_26);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_usize_of_nat(x_11);
x_36 = lean_usize_add(x_5, x_35);
x_37 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1_spec__1(x_1, x_2, x_3, x_4, x_36, x_33, x_7, x_34);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_5 = lean_unsigned_to_nat(5u);
x_6 = l_Lean_Syntax_getArg(x_2, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_Syntax_getArg(x_6, x_7);
lean_dec(x_6);
x_9 = l_Lean_Syntax_getArgs(x_8);
lean_dec(x_8);
x_10 = lean_mk_empty_array_with_capacity(x_7);
x_11 = lean_unsigned_to_nat(1u);
lean_inc(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_array_size(x_9);
x_15 = lean_usize_of_nat(x_7);
x_16 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1(x_2, x_1, x_9, x_14, x_15, x_13, x_3, x_4);
lean_dec(x_9);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_16, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_dec(x_24);
x_25 = lean_mk_string_unchecked("Lean", 4, 4);
x_26 = lean_mk_string_unchecked("Parser", 6, 6);
x_27 = lean_mk_string_unchecked("Term", 4, 4);
x_28 = lean_mk_string_unchecked("match", 5, 5);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
x_29 = l_Lean_Name_mkStr4(x_25, x_26, x_27, x_28);
x_30 = l_Lean_Syntax_setKind(x_2, x_29);
x_31 = lean_mk_string_unchecked("matchAlts", 9, 9);
x_32 = l_Lean_Name_mkStr4(x_25, x_26, x_27, x_31);
x_33 = lean_mk_string_unchecked("null", 4, 4);
x_34 = l_Lean_Name_mkStr1(x_33);
x_35 = lean_box(2);
x_36 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_36, 2, x_21);
x_37 = lean_mk_empty_array_with_capacity(x_11);
x_38 = lean_array_push(x_37, x_36);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_32);
lean_ctor_set(x_39, 2, x_38);
x_40 = l_Lean_Syntax_setArg(x_30, x_5, x_39);
lean_ctor_set(x_18, 1, x_23);
lean_ctor_set(x_18, 0, x_40);
lean_ctor_set(x_16, 0, x_18);
return x_16;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_41 = lean_ctor_get(x_18, 0);
lean_inc(x_41);
lean_dec(x_18);
x_42 = lean_mk_string_unchecked("Lean", 4, 4);
x_43 = lean_mk_string_unchecked("Parser", 6, 6);
x_44 = lean_mk_string_unchecked("Term", 4, 4);
x_45 = lean_mk_string_unchecked("match", 5, 5);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
x_46 = l_Lean_Name_mkStr4(x_42, x_43, x_44, x_45);
x_47 = l_Lean_Syntax_setKind(x_2, x_46);
x_48 = lean_mk_string_unchecked("matchAlts", 9, 9);
x_49 = l_Lean_Name_mkStr4(x_42, x_43, x_44, x_48);
x_50 = lean_mk_string_unchecked("null", 4, 4);
x_51 = l_Lean_Name_mkStr1(x_50);
x_52 = lean_box(2);
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
lean_ctor_set(x_53, 2, x_21);
x_54 = lean_mk_empty_array_with_capacity(x_11);
x_55 = lean_array_push(x_54, x_53);
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_52);
lean_ctor_set(x_56, 1, x_49);
lean_ctor_set(x_56, 2, x_55);
x_57 = l_Lean_Syntax_setArg(x_47, x_5, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_41);
lean_ctor_set(x_16, 0, x_58);
return x_16;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_59 = lean_ctor_get(x_16, 1);
lean_inc(x_59);
lean_dec(x_16);
x_60 = lean_ctor_get(x_17, 0);
lean_inc(x_60);
lean_dec(x_17);
x_61 = lean_ctor_get(x_18, 0);
lean_inc(x_61);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_62 = x_18;
} else {
 lean_dec_ref(x_18);
 x_62 = lean_box(0);
}
x_63 = lean_mk_string_unchecked("Lean", 4, 4);
x_64 = lean_mk_string_unchecked("Parser", 6, 6);
x_65 = lean_mk_string_unchecked("Term", 4, 4);
x_66 = lean_mk_string_unchecked("match", 5, 5);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
x_67 = l_Lean_Name_mkStr4(x_63, x_64, x_65, x_66);
x_68 = l_Lean_Syntax_setKind(x_2, x_67);
x_69 = lean_mk_string_unchecked("matchAlts", 9, 9);
x_70 = l_Lean_Name_mkStr4(x_63, x_64, x_65, x_69);
x_71 = lean_mk_string_unchecked("null", 4, 4);
x_72 = l_Lean_Name_mkStr1(x_71);
x_73 = lean_box(2);
x_74 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
lean_ctor_set(x_74, 2, x_60);
x_75 = lean_mk_empty_array_with_capacity(x_11);
x_76 = lean_array_push(x_75, x_74);
x_77 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_77, 0, x_73);
lean_ctor_set(x_77, 1, x_70);
lean_ctor_set(x_77, 2, x_76);
x_78 = l_Lean_Syntax_setArg(x_68, x_5, x_77);
if (lean_is_scalar(x_62)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_62;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_61);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_59);
return x_80;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_12 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_13 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0(x_1, x_2, x_3, x_4, x_5, x_11, x_12, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1_spec__1(x_1, x_2, x_3, x_9, x_10, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1(x_1, x_2, x_3, x_9, x_10, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalMatch___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_2);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_ctor_get_uint8(x_5, sizeof(void*)*7);
x_17 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 1);
x_18 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 2);
x_19 = lean_ctor_get(x_5, 2);
x_20 = lean_ctor_get(x_5, 3);
x_21 = lean_ctor_get(x_5, 4);
x_22 = lean_ctor_get(x_5, 5);
x_23 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 3);
x_24 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 4);
x_25 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 5);
x_26 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 6);
x_27 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 7);
x_28 = lean_ctor_get(x_5, 6);
x_29 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 8);
x_30 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 9);
x_31 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 10);
lean_inc(x_28);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_12);
x_32 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_32, 0, x_12);
lean_ctor_set(x_32, 1, x_15);
lean_ctor_set(x_32, 2, x_19);
lean_ctor_set(x_32, 3, x_20);
lean_ctor_set(x_32, 4, x_21);
lean_ctor_set(x_32, 5, x_22);
lean_ctor_set(x_32, 6, x_28);
lean_ctor_set_uint8(x_32, sizeof(void*)*7, x_16);
lean_ctor_set_uint8(x_32, sizeof(void*)*7 + 1, x_17);
lean_ctor_set_uint8(x_32, sizeof(void*)*7 + 2, x_18);
lean_ctor_set_uint8(x_32, sizeof(void*)*7 + 3, x_23);
lean_ctor_set_uint8(x_32, sizeof(void*)*7 + 4, x_24);
lean_ctor_set_uint8(x_32, sizeof(void*)*7 + 5, x_25);
lean_ctor_set_uint8(x_32, sizeof(void*)*7 + 6, x_26);
lean_ctor_set_uint8(x_32, sizeof(void*)*7 + 7, x_27);
lean_ctor_set_uint8(x_32, sizeof(void*)*7 + 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*7 + 9, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*7 + 10, x_31);
x_33 = l_Lean_Elab_Tactic_evalTactic(x_2, x_3, x_4, x_32, x_6, x_7, x_8, x_9, x_10, x_11);
return x_33;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm), 4, 2);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_1);
lean_inc(x_8);
x_15 = l_Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 1);
x_21 = lean_st_ref_get(x_9, x_17);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_23 = lean_ctor_get(x_21, 1);
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_8, 5);
lean_inc(x_25);
x_26 = lean_box(0);
x_27 = lean_unbox(x_26);
x_28 = l_Lean_SourceInfo_fromRef(x_25, x_27);
lean_dec(x_25);
x_29 = lean_mk_string_unchecked("Lean", 4, 4);
x_30 = lean_mk_string_unchecked("Parser", 6, 6);
x_31 = lean_mk_string_unchecked("Tactic", 6, 6);
x_32 = lean_mk_string_unchecked("refine", 6, 6);
lean_inc(x_32);
lean_inc(x_30);
lean_inc(x_29);
x_33 = l_Lean_Name_mkStr4(x_29, x_30, x_31, x_32);
lean_inc(x_28);
lean_ctor_set_tag(x_21, 2);
lean_ctor_set(x_21, 1, x_32);
lean_ctor_set(x_21, 0, x_28);
x_34 = lean_mk_string_unchecked("Term", 4, 4);
x_35 = lean_mk_string_unchecked("noImplicitLambda", 16, 16);
x_36 = l_Lean_Name_mkStr4(x_29, x_30, x_34, x_35);
x_37 = lean_mk_string_unchecked("no_implicit_lambda%", 19, 19);
lean_inc(x_28);
lean_ctor_set_tag(x_16, 2);
lean_ctor_set(x_16, 1, x_37);
lean_ctor_set(x_16, 0, x_28);
lean_inc(x_28);
x_38 = l_Lean_Syntax_node2(x_28, x_36, x_16, x_19);
x_39 = l_Lean_Syntax_node2(x_28, x_33, x_21, x_38);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_mk_empty_array_with_capacity(x_40);
x_42 = lean_array_push(x_41, x_39);
x_43 = l_Array_append(lean_box(0), x_42, x_20);
lean_dec(x_20);
x_44 = lean_mk_string_unchecked("null", 4, 4);
x_45 = l_Lean_Name_mkStr1(x_44);
x_46 = lean_box(2);
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set(x_47, 2, x_43);
lean_inc(x_47);
lean_inc(x_1);
x_48 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalMatch___lam__0___boxed), 11, 2);
lean_closure_set(x_48, 0, x_1);
lean_closure_set(x_48, 1, x_47);
x_49 = l_Lean_Elab_withMacroExpansionInfo___at___Lean_Elab_Tactic_adaptExpander_spec__0___redArg(x_1, x_47, x_48, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_50 = lean_ctor_get(x_21, 1);
lean_inc(x_50);
lean_dec(x_21);
x_51 = lean_ctor_get(x_8, 5);
lean_inc(x_51);
x_52 = lean_box(0);
x_53 = lean_unbox(x_52);
x_54 = l_Lean_SourceInfo_fromRef(x_51, x_53);
lean_dec(x_51);
x_55 = lean_mk_string_unchecked("Lean", 4, 4);
x_56 = lean_mk_string_unchecked("Parser", 6, 6);
x_57 = lean_mk_string_unchecked("Tactic", 6, 6);
x_58 = lean_mk_string_unchecked("refine", 6, 6);
lean_inc(x_58);
lean_inc(x_56);
lean_inc(x_55);
x_59 = l_Lean_Name_mkStr4(x_55, x_56, x_57, x_58);
lean_inc(x_54);
x_60 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_60, 0, x_54);
lean_ctor_set(x_60, 1, x_58);
x_61 = lean_mk_string_unchecked("Term", 4, 4);
x_62 = lean_mk_string_unchecked("noImplicitLambda", 16, 16);
x_63 = l_Lean_Name_mkStr4(x_55, x_56, x_61, x_62);
x_64 = lean_mk_string_unchecked("no_implicit_lambda%", 19, 19);
lean_inc(x_54);
lean_ctor_set_tag(x_16, 2);
lean_ctor_set(x_16, 1, x_64);
lean_ctor_set(x_16, 0, x_54);
lean_inc(x_54);
x_65 = l_Lean_Syntax_node2(x_54, x_63, x_16, x_19);
x_66 = l_Lean_Syntax_node2(x_54, x_59, x_60, x_65);
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_mk_empty_array_with_capacity(x_67);
x_69 = lean_array_push(x_68, x_66);
x_70 = l_Array_append(lean_box(0), x_69, x_20);
lean_dec(x_20);
x_71 = lean_mk_string_unchecked("null", 4, 4);
x_72 = l_Lean_Name_mkStr1(x_71);
x_73 = lean_box(2);
x_74 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
lean_ctor_set(x_74, 2, x_70);
lean_inc(x_74);
lean_inc(x_1);
x_75 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalMatch___lam__0___boxed), 11, 2);
lean_closure_set(x_75, 0, x_1);
lean_closure_set(x_75, 1, x_74);
x_76 = l_Lean_Elab_withMacroExpansionInfo___at___Lean_Elab_Tactic_adaptExpander_spec__0___redArg(x_1, x_74, x_75, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_50);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_77 = lean_ctor_get(x_16, 0);
x_78 = lean_ctor_get(x_16, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_16);
x_79 = lean_st_ref_get(x_9, x_17);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_81 = x_79;
} else {
 lean_dec_ref(x_79);
 x_81 = lean_box(0);
}
x_82 = lean_ctor_get(x_8, 5);
lean_inc(x_82);
x_83 = lean_box(0);
x_84 = lean_unbox(x_83);
x_85 = l_Lean_SourceInfo_fromRef(x_82, x_84);
lean_dec(x_82);
x_86 = lean_mk_string_unchecked("Lean", 4, 4);
x_87 = lean_mk_string_unchecked("Parser", 6, 6);
x_88 = lean_mk_string_unchecked("Tactic", 6, 6);
x_89 = lean_mk_string_unchecked("refine", 6, 6);
lean_inc(x_89);
lean_inc(x_87);
lean_inc(x_86);
x_90 = l_Lean_Name_mkStr4(x_86, x_87, x_88, x_89);
lean_inc(x_85);
if (lean_is_scalar(x_81)) {
 x_91 = lean_alloc_ctor(2, 2, 0);
} else {
 x_91 = x_81;
 lean_ctor_set_tag(x_91, 2);
}
lean_ctor_set(x_91, 0, x_85);
lean_ctor_set(x_91, 1, x_89);
x_92 = lean_mk_string_unchecked("Term", 4, 4);
x_93 = lean_mk_string_unchecked("noImplicitLambda", 16, 16);
x_94 = l_Lean_Name_mkStr4(x_86, x_87, x_92, x_93);
x_95 = lean_mk_string_unchecked("no_implicit_lambda%", 19, 19);
lean_inc(x_85);
x_96 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_96, 0, x_85);
lean_ctor_set(x_96, 1, x_95);
lean_inc(x_85);
x_97 = l_Lean_Syntax_node2(x_85, x_94, x_96, x_77);
x_98 = l_Lean_Syntax_node2(x_85, x_90, x_91, x_97);
x_99 = lean_unsigned_to_nat(1u);
x_100 = lean_mk_empty_array_with_capacity(x_99);
x_101 = lean_array_push(x_100, x_98);
x_102 = l_Array_append(lean_box(0), x_101, x_78);
lean_dec(x_78);
x_103 = lean_mk_string_unchecked("null", 4, 4);
x_104 = l_Lean_Name_mkStr1(x_103);
x_105 = lean_box(2);
x_106 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
lean_ctor_set(x_106, 2, x_102);
lean_inc(x_106);
lean_inc(x_1);
x_107 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalMatch___lam__0___boxed), 11, 2);
lean_closure_set(x_107, 0, x_1);
lean_closure_set(x_107, 1, x_106);
x_108 = l_Lean_Elab_withMacroExpansionInfo___at___Lean_Elab_Tactic_adaptExpander_spec__0___redArg(x_1, x_106, x_107, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_80);
return x_108;
}
}
else
{
uint8_t x_109; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_15);
if (x_109 == 0)
{
return x_15;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_15, 0);
x_111 = lean_ctor_get(x_15, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_15);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_113 = !lean_is_exclusive(x_11);
if (x_113 == 0)
{
return x_11;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_11, 0);
x_115 = lean_ctor_get(x_11, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_11);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalMatch___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_evalMatch___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalMatch__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("match", 5, 5);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("evalMatch", 9, 9);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalMatch), 10, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("evalMatch", 9, 9);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(53u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(58u);
x_11 = lean_unsigned_to_nat(52u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(4u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(13u);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_addBuiltinDeclarationRanges(x_6, x_19, x_1);
return x_20;
}
}
lean_object* initialize_Lean_Parser_Term(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Match(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Induction(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Match(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Term(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Match(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Induction(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalMatch__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
