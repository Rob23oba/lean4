// Lean compiler output
// Module: Lean.Elab.MacroRules
// Imports: Lean.Elab.Syntax Lean.Elab.AuxDef
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getQuotContent(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRulesAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRulesAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandNoKindMacroRulesAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabMacroRules__1(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabMacroRulesAux_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_resolveSyntaxKind(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_ofElems(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabMacroRulesAux_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isQuot(lean_object*);
lean_object* l_Lean_Elab_Command_adaptExpander(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Command_checkRuleKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabMacroRulesAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getMainModule___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Syntax_node8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabMacroRulesAux_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
extern lean_object* l_Lean_instInhabitedSyntax;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__1(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabMacroRulesAux_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = lean_array_uget(x_2, x_4);
lean_inc(x_8);
x_9 = l_Lean_Syntax_getKind(x_8);
lean_inc(x_1);
x_10 = l_Lean_Elab_Command_checkRuleKind(x_9, x_1);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_usize_of_nat(x_13);
x_15 = lean_usize_add(x_4, x_14);
x_4 = x_15;
x_5 = x_12;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_8);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_7);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_20; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_10 = lean_box(0);
lean_inc(x_4);
x_11 = lean_array_uset(x_4, x_3, x_10);
x_26 = lean_array_uget(x_4, x_3);
lean_dec(x_4);
x_39 = lean_mk_string_unchecked("Lean", 4, 4);
x_40 = lean_mk_string_unchecked("Parser", 6, 6);
x_41 = lean_mk_string_unchecked("Term", 4, 4);
x_42 = lean_mk_string_unchecked("matchAlt", 8, 8);
x_43 = l_Lean_Name_mkStr4(x_39, x_40, x_41, x_42);
lean_inc(x_26);
x_44 = l_Lean_Syntax_isOfKind(x_26, x_43);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_43);
lean_dec(x_26);
lean_dec(x_11);
lean_dec(x_1);
x_45 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_5, x_6, x_7);
x_20 = x_45;
goto block_25;
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_unsigned_to_nat(1u);
x_47 = l_Lean_Syntax_getArg(x_26, x_46);
lean_inc(x_47);
x_48 = l_Lean_Syntax_matchesNull(x_47, x_46);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_47);
lean_dec(x_43);
lean_dec(x_26);
lean_dec(x_11);
lean_dec(x_1);
x_49 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_5, x_6, x_7);
x_20 = x_49;
goto block_25;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_140; 
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Lean_Syntax_getArg(x_47, x_50);
lean_dec(x_47);
x_52 = lean_unsigned_to_nat(3u);
x_53 = l_Lean_Syntax_getArg(x_26, x_52);
x_54 = l_Lean_Syntax_getArgs(x_51);
lean_dec(x_51);
x_55 = l_Lean_instInhabitedSyntax;
x_56 = lean_array_get(x_55, x_54, x_50);
x_140 = l_Lean_Syntax_isQuot(x_56);
if (x_140 == 0)
{
if (x_48 == 0)
{
x_57 = x_5;
x_58 = x_6;
x_59 = x_7;
goto block_139;
}
else
{
lean_object* x_141; uint8_t x_142; 
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_43);
lean_dec(x_26);
lean_dec(x_11);
lean_dec(x_1);
x_141 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_5, x_6, x_7);
x_142 = !lean_is_exclusive(x_141);
if (x_142 == 0)
{
return x_141;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_141, 0);
x_144 = lean_ctor_get(x_141, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_141);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
else
{
x_57 = x_5;
x_58 = x_6;
x_59 = x_7;
goto block_139;
}
block_139:
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
lean_inc(x_56);
x_60 = l_Lean_Syntax_getQuotContent(x_56);
lean_inc(x_60);
x_61 = l_Lean_Syntax_getKind(x_60);
lean_inc(x_1);
x_62 = l_Lean_Elab_Command_checkRuleKind(x_61, x_1);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = lean_mk_string_unchecked("choice", 6, 6);
x_64 = l_Lean_Name_mkStr1(x_63);
x_65 = lean_name_eq(x_61, x_64);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_60);
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_43);
lean_dec(x_11);
lean_dec(x_1);
x_66 = lean_mk_string_unchecked("invalid macro_rules alternative, unexpected syntax node kind '", 62, 62);
x_67 = l_Lean_stringToMessageData(x_66);
lean_dec(x_66);
x_68 = l_Lean_MessageData_ofName(x_61);
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_mk_string_unchecked("'", 1, 1);
x_71 = l_Lean_stringToMessageData(x_70);
lean_dec(x_70);
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_26, x_72, x_57, x_58, x_59);
lean_dec(x_26);
x_20 = x_73;
goto block_25;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; size_t x_78; size_t x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_61);
x_74 = l_Lean_Syntax_getArgs(x_60);
lean_dec(x_60);
x_75 = lean_box(0);
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_array_size(x_74);
x_79 = lean_usize_of_nat(x_50);
lean_inc(x_1);
x_80 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabMacroRulesAux_spec__0(x_1, x_74, x_78, x_79, x_77);
lean_dec(x_74);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec(x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_43);
lean_dec(x_11);
x_27 = x_57;
x_28 = x_59;
x_29 = x_58;
goto block_38;
}
else
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec(x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_43);
lean_dec(x_11);
x_27 = x_57;
x_28 = x_59;
x_29 = x_58;
goto block_38;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
lean_dec(x_26);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec(x_82);
x_84 = l_Lean_Elab_Command_getRef(x_57, x_58, x_59);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_Lean_Elab_Command_getCurrMacroScope(x_57, x_58, x_86);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_89 = lean_ctor_get(x_87, 1);
x_90 = lean_ctor_get(x_87, 0);
lean_dec(x_90);
x_91 = l_Lean_Elab_Command_getMainModule___redArg(x_58, x_89);
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_93 = lean_ctor_get(x_91, 1);
x_94 = lean_ctor_get(x_91, 0);
lean_dec(x_94);
x_95 = l_Lean_Syntax_setArg(x_56, x_46, x_83);
x_96 = lean_array_set(x_54, x_50, x_95);
x_97 = l_Lean_SourceInfo_fromRef(x_85, x_62);
lean_dec(x_85);
x_98 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_97);
lean_ctor_set_tag(x_91, 2);
lean_ctor_set(x_91, 1, x_98);
lean_ctor_set(x_91, 0, x_97);
x_99 = lean_mk_string_unchecked("null", 4, 4);
x_100 = l_Lean_Name_mkStr1(x_99);
x_101 = l_Array_mkArray0(lean_box(0));
x_102 = l_Array_append(lean_box(0), x_101, x_96);
lean_dec(x_96);
lean_inc(x_100);
lean_inc(x_97);
x_103 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_103, 0, x_97);
lean_ctor_set(x_103, 1, x_100);
lean_ctor_set(x_103, 2, x_102);
lean_inc(x_97);
x_104 = l_Lean_Syntax_node1(x_97, x_100, x_103);
x_105 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_97);
lean_ctor_set_tag(x_87, 2);
lean_ctor_set(x_87, 1, x_105);
lean_ctor_set(x_87, 0, x_97);
x_106 = l_Lean_Syntax_node4(x_97, x_43, x_91, x_104, x_87, x_53);
x_12 = x_106;
x_13 = x_93;
goto block_19;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_107 = lean_ctor_get(x_91, 1);
lean_inc(x_107);
lean_dec(x_91);
x_108 = l_Lean_Syntax_setArg(x_56, x_46, x_83);
x_109 = lean_array_set(x_54, x_50, x_108);
x_110 = l_Lean_SourceInfo_fromRef(x_85, x_62);
lean_dec(x_85);
x_111 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_110);
x_112 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_mk_string_unchecked("null", 4, 4);
x_114 = l_Lean_Name_mkStr1(x_113);
x_115 = l_Array_mkArray0(lean_box(0));
x_116 = l_Array_append(lean_box(0), x_115, x_109);
lean_dec(x_109);
lean_inc(x_114);
lean_inc(x_110);
x_117 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_117, 0, x_110);
lean_ctor_set(x_117, 1, x_114);
lean_ctor_set(x_117, 2, x_116);
lean_inc(x_110);
x_118 = l_Lean_Syntax_node1(x_110, x_114, x_117);
x_119 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_110);
lean_ctor_set_tag(x_87, 2);
lean_ctor_set(x_87, 1, x_119);
lean_ctor_set(x_87, 0, x_110);
x_120 = l_Lean_Syntax_node4(x_110, x_43, x_112, x_118, x_87, x_53);
x_12 = x_120;
x_13 = x_107;
goto block_19;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_121 = lean_ctor_get(x_87, 1);
lean_inc(x_121);
lean_dec(x_87);
x_122 = l_Lean_Elab_Command_getMainModule___redArg(x_58, x_121);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_124 = x_122;
} else {
 lean_dec_ref(x_122);
 x_124 = lean_box(0);
}
x_125 = l_Lean_Syntax_setArg(x_56, x_46, x_83);
x_126 = lean_array_set(x_54, x_50, x_125);
x_127 = l_Lean_SourceInfo_fromRef(x_85, x_62);
lean_dec(x_85);
x_128 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_127);
if (lean_is_scalar(x_124)) {
 x_129 = lean_alloc_ctor(2, 2, 0);
} else {
 x_129 = x_124;
 lean_ctor_set_tag(x_129, 2);
}
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_mk_string_unchecked("null", 4, 4);
x_131 = l_Lean_Name_mkStr1(x_130);
x_132 = l_Array_mkArray0(lean_box(0));
x_133 = l_Array_append(lean_box(0), x_132, x_126);
lean_dec(x_126);
lean_inc(x_131);
lean_inc(x_127);
x_134 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_134, 0, x_127);
lean_ctor_set(x_134, 1, x_131);
lean_ctor_set(x_134, 2, x_133);
lean_inc(x_127);
x_135 = l_Lean_Syntax_node1(x_127, x_131, x_134);
x_136 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_127);
x_137 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_137, 0, x_127);
lean_ctor_set(x_137, 1, x_136);
x_138 = l_Lean_Syntax_node4(x_127, x_43, x_129, x_135, x_137, x_53);
x_12 = x_138;
x_13 = x_123;
goto block_19;
}
}
}
}
}
else
{
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_43);
x_12 = x_26;
x_13 = x_59;
goto block_19;
}
}
}
}
block_19:
{
lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_3, x_15);
x_17 = lean_array_uset(x_11, x_3, x_12);
x_3 = x_16;
x_4 = x_17;
x_7 = x_13;
goto _start;
}
block_25:
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
block_38:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_mk_string_unchecked("invalid macro_rules alternative, expected syntax node kind '", 60, 60);
x_31 = l_Lean_stringToMessageData(x_30);
lean_dec(x_30);
x_32 = l_Lean_MessageData_ofName(x_1);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_mk_string_unchecked("'", 1, 1);
x_35 = l_Lean_stringToMessageData(x_34);
lean_dec(x_34);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_26, x_36, x_27, x_29, x_28);
lean_dec(x_26);
x_20 = x_37;
goto block_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabMacroRulesAux_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_20; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_10 = lean_box(0);
lean_inc(x_4);
x_11 = lean_array_uset(x_4, x_3, x_10);
x_26 = lean_array_uget(x_4, x_3);
lean_dec(x_4);
x_39 = lean_mk_string_unchecked("Lean", 4, 4);
x_40 = lean_mk_string_unchecked("Parser", 6, 6);
x_41 = lean_mk_string_unchecked("Term", 4, 4);
x_42 = lean_mk_string_unchecked("matchAlt", 8, 8);
x_43 = l_Lean_Name_mkStr4(x_39, x_40, x_41, x_42);
lean_inc(x_26);
x_44 = l_Lean_Syntax_isOfKind(x_26, x_43);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_43);
lean_dec(x_26);
lean_dec(x_11);
lean_dec(x_1);
x_45 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_5, x_6, x_7);
x_20 = x_45;
goto block_25;
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_unsigned_to_nat(1u);
x_47 = l_Lean_Syntax_getArg(x_26, x_46);
lean_inc(x_47);
x_48 = l_Lean_Syntax_matchesNull(x_47, x_46);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_47);
lean_dec(x_43);
lean_dec(x_26);
lean_dec(x_11);
lean_dec(x_1);
x_49 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_5, x_6, x_7);
x_20 = x_49;
goto block_25;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_140; 
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Lean_Syntax_getArg(x_47, x_50);
lean_dec(x_47);
x_52 = lean_unsigned_to_nat(3u);
x_53 = l_Lean_Syntax_getArg(x_26, x_52);
x_54 = l_Lean_Syntax_getArgs(x_51);
lean_dec(x_51);
x_55 = l_Lean_instInhabitedSyntax;
x_56 = lean_array_get(x_55, x_54, x_50);
x_140 = l_Lean_Syntax_isQuot(x_56);
if (x_140 == 0)
{
if (x_48 == 0)
{
x_57 = x_5;
x_58 = x_6;
x_59 = x_7;
goto block_139;
}
else
{
lean_object* x_141; uint8_t x_142; 
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_43);
lean_dec(x_26);
lean_dec(x_11);
lean_dec(x_1);
x_141 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_5, x_6, x_7);
x_142 = !lean_is_exclusive(x_141);
if (x_142 == 0)
{
return x_141;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_141, 0);
x_144 = lean_ctor_get(x_141, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_141);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
else
{
x_57 = x_5;
x_58 = x_6;
x_59 = x_7;
goto block_139;
}
block_139:
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
lean_inc(x_56);
x_60 = l_Lean_Syntax_getQuotContent(x_56);
lean_inc(x_60);
x_61 = l_Lean_Syntax_getKind(x_60);
lean_inc(x_1);
x_62 = l_Lean_Elab_Command_checkRuleKind(x_61, x_1);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = lean_mk_string_unchecked("choice", 6, 6);
x_64 = l_Lean_Name_mkStr1(x_63);
x_65 = lean_name_eq(x_61, x_64);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_60);
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_43);
lean_dec(x_11);
lean_dec(x_1);
x_66 = lean_mk_string_unchecked("invalid macro_rules alternative, unexpected syntax node kind '", 62, 62);
x_67 = l_Lean_stringToMessageData(x_66);
lean_dec(x_66);
x_68 = l_Lean_MessageData_ofName(x_61);
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_mk_string_unchecked("'", 1, 1);
x_71 = l_Lean_stringToMessageData(x_70);
lean_dec(x_70);
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_26, x_72, x_57, x_58, x_59);
lean_dec(x_26);
x_20 = x_73;
goto block_25;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; size_t x_78; size_t x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_61);
x_74 = l_Lean_Syntax_getArgs(x_60);
lean_dec(x_60);
x_75 = lean_box(0);
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_array_size(x_74);
x_79 = lean_usize_of_nat(x_50);
lean_inc(x_1);
x_80 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabMacroRulesAux_spec__0(x_1, x_74, x_78, x_79, x_77);
lean_dec(x_74);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec(x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_43);
lean_dec(x_11);
x_27 = x_58;
x_28 = x_59;
x_29 = x_57;
goto block_38;
}
else
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec(x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_43);
lean_dec(x_11);
x_27 = x_58;
x_28 = x_59;
x_29 = x_57;
goto block_38;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
lean_dec(x_26);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec(x_82);
x_84 = l_Lean_Elab_Command_getRef(x_57, x_58, x_59);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_Lean_Elab_Command_getCurrMacroScope(x_57, x_58, x_86);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_89 = lean_ctor_get(x_87, 1);
x_90 = lean_ctor_get(x_87, 0);
lean_dec(x_90);
x_91 = l_Lean_Elab_Command_getMainModule___redArg(x_58, x_89);
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_93 = lean_ctor_get(x_91, 1);
x_94 = lean_ctor_get(x_91, 0);
lean_dec(x_94);
x_95 = l_Lean_Syntax_setArg(x_56, x_46, x_83);
x_96 = lean_array_set(x_54, x_50, x_95);
x_97 = l_Lean_SourceInfo_fromRef(x_85, x_62);
lean_dec(x_85);
x_98 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_97);
lean_ctor_set_tag(x_91, 2);
lean_ctor_set(x_91, 1, x_98);
lean_ctor_set(x_91, 0, x_97);
x_99 = lean_mk_string_unchecked("null", 4, 4);
x_100 = l_Lean_Name_mkStr1(x_99);
x_101 = l_Array_mkArray0(lean_box(0));
x_102 = l_Array_append(lean_box(0), x_101, x_96);
lean_dec(x_96);
lean_inc(x_100);
lean_inc(x_97);
x_103 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_103, 0, x_97);
lean_ctor_set(x_103, 1, x_100);
lean_ctor_set(x_103, 2, x_102);
lean_inc(x_97);
x_104 = l_Lean_Syntax_node1(x_97, x_100, x_103);
x_105 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_97);
lean_ctor_set_tag(x_87, 2);
lean_ctor_set(x_87, 1, x_105);
lean_ctor_set(x_87, 0, x_97);
x_106 = l_Lean_Syntax_node4(x_97, x_43, x_91, x_104, x_87, x_53);
x_12 = x_106;
x_13 = x_93;
goto block_19;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_107 = lean_ctor_get(x_91, 1);
lean_inc(x_107);
lean_dec(x_91);
x_108 = l_Lean_Syntax_setArg(x_56, x_46, x_83);
x_109 = lean_array_set(x_54, x_50, x_108);
x_110 = l_Lean_SourceInfo_fromRef(x_85, x_62);
lean_dec(x_85);
x_111 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_110);
x_112 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_mk_string_unchecked("null", 4, 4);
x_114 = l_Lean_Name_mkStr1(x_113);
x_115 = l_Array_mkArray0(lean_box(0));
x_116 = l_Array_append(lean_box(0), x_115, x_109);
lean_dec(x_109);
lean_inc(x_114);
lean_inc(x_110);
x_117 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_117, 0, x_110);
lean_ctor_set(x_117, 1, x_114);
lean_ctor_set(x_117, 2, x_116);
lean_inc(x_110);
x_118 = l_Lean_Syntax_node1(x_110, x_114, x_117);
x_119 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_110);
lean_ctor_set_tag(x_87, 2);
lean_ctor_set(x_87, 1, x_119);
lean_ctor_set(x_87, 0, x_110);
x_120 = l_Lean_Syntax_node4(x_110, x_43, x_112, x_118, x_87, x_53);
x_12 = x_120;
x_13 = x_107;
goto block_19;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_121 = lean_ctor_get(x_87, 1);
lean_inc(x_121);
lean_dec(x_87);
x_122 = l_Lean_Elab_Command_getMainModule___redArg(x_58, x_121);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_124 = x_122;
} else {
 lean_dec_ref(x_122);
 x_124 = lean_box(0);
}
x_125 = l_Lean_Syntax_setArg(x_56, x_46, x_83);
x_126 = lean_array_set(x_54, x_50, x_125);
x_127 = l_Lean_SourceInfo_fromRef(x_85, x_62);
lean_dec(x_85);
x_128 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_127);
if (lean_is_scalar(x_124)) {
 x_129 = lean_alloc_ctor(2, 2, 0);
} else {
 x_129 = x_124;
 lean_ctor_set_tag(x_129, 2);
}
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_mk_string_unchecked("null", 4, 4);
x_131 = l_Lean_Name_mkStr1(x_130);
x_132 = l_Array_mkArray0(lean_box(0));
x_133 = l_Array_append(lean_box(0), x_132, x_126);
lean_dec(x_126);
lean_inc(x_131);
lean_inc(x_127);
x_134 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_134, 0, x_127);
lean_ctor_set(x_134, 1, x_131);
lean_ctor_set(x_134, 2, x_133);
lean_inc(x_127);
x_135 = l_Lean_Syntax_node1(x_127, x_131, x_134);
x_136 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_127);
x_137 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_137, 0, x_127);
lean_ctor_set(x_137, 1, x_136);
x_138 = l_Lean_Syntax_node4(x_127, x_43, x_129, x_135, x_137, x_53);
x_12 = x_138;
x_13 = x_123;
goto block_19;
}
}
}
}
}
else
{
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_43);
x_12 = x_26;
x_13 = x_59;
goto block_19;
}
}
}
}
block_19:
{
lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_3, x_15);
x_17 = lean_array_uset(x_11, x_3, x_12);
x_18 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1(x_1, x_2, x_16, x_17, x_5, x_6, x_13);
return x_18;
}
block_25:
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
block_38:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_mk_string_unchecked("invalid macro_rules alternative, expected syntax node kind '", 60, 60);
x_31 = l_Lean_stringToMessageData(x_30);
lean_dec(x_30);
x_32 = l_Lean_MessageData_ofName(x_1);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_mk_string_unchecked("'", 1, 1);
x_35 = l_Lean_stringToMessageData(x_34);
lean_dec(x_34);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_26, x_36, x_29, x_27, x_28);
lean_dec(x_26);
x_20 = x_37;
goto block_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRulesAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; lean_object* x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_array_size(x_6);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_usize_of_nat(x_11);
lean_inc(x_5);
x_13 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabMacroRulesAux_spec__1(x_5, x_10, x_12, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_16 = x_13;
} else {
 lean_dec_ref(x_13);
 x_16 = lean_box(0);
}
x_124 = l_Lean_Elab_Command_getRef(x_7, x_8, x_15);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_127 = l_Lean_Elab_Command_getCurrMacroScope(x_7, x_8, x_126);
x_128 = !lean_is_exclusive(x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_129 = lean_ctor_get(x_127, 1);
x_130 = lean_ctor_get(x_127, 0);
lean_dec(x_130);
x_131 = l_Lean_Elab_Command_getMainModule___redArg(x_8, x_129);
x_132 = !lean_is_exclusive(x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_133 = lean_ctor_get(x_131, 1);
x_134 = lean_ctor_get(x_131, 0);
lean_dec(x_134);
x_135 = lean_box(0);
x_160 = lean_unbox(x_135);
x_161 = l_Lean_SourceInfo_fromRef(x_125, x_160);
lean_dec(x_125);
x_162 = lean_mk_string_unchecked("Lean", 4, 4);
x_163 = lean_mk_string_unchecked("Parser", 6, 6);
x_164 = lean_mk_string_unchecked("Term", 4, 4);
x_165 = lean_mk_string_unchecked("attrInstance", 12, 12);
lean_inc(x_163);
lean_inc(x_162);
x_166 = l_Lean_Name_mkStr4(x_162, x_163, x_164, x_165);
x_167 = lean_box(0);
lean_inc(x_166);
lean_ctor_set_tag(x_131, 1);
lean_ctor_set(x_131, 1, x_167);
lean_ctor_set(x_131, 0, x_166);
x_168 = lean_mk_string_unchecked("Attr", 4, 4);
x_169 = lean_mk_string_unchecked("macro", 5, 5);
lean_inc(x_169);
x_170 = l_Lean_Name_mkStr4(x_162, x_163, x_168, x_169);
lean_inc(x_161);
lean_ctor_set_tag(x_127, 2);
lean_ctor_set(x_127, 1, x_169);
lean_ctor_set(x_127, 0, x_161);
lean_inc(x_5);
x_171 = lean_mk_syntax_ident(x_5);
lean_inc(x_161);
x_172 = l_Lean_Syntax_node2(x_161, x_170, x_127, x_171);
x_173 = l_Lean_Syntax_node2(x_161, x_166, x_3, x_172);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_174 = lean_mk_string_unchecked(",", 1, 1);
x_175 = lean_unsigned_to_nat(1u);
x_176 = lean_mk_empty_array_with_capacity(x_175);
x_177 = lean_array_push(x_176, x_173);
x_178 = l_Lean_Syntax_TSepArray_ofElems(x_131, x_174, x_177);
lean_dec(x_177);
lean_dec(x_131);
x_136 = x_178;
goto block_159;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_179 = lean_ctor_get(x_2, 0);
x_180 = lean_mk_string_unchecked(",", 1, 1);
x_181 = l_Lean_Syntax_TSepArray_getElems___redArg(x_179);
x_182 = lean_array_push(x_181, x_173);
x_183 = l_Lean_Syntax_TSepArray_ofElems(x_131, x_180, x_182);
lean_dec(x_182);
lean_dec(x_131);
x_136 = x_183;
goto block_159;
}
block_159:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_137 = l_Lean_Elab_Command_getRef(x_7, x_8, x_133);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_140 = l_Lean_Elab_Command_getCurrMacroScope(x_7, x_8, x_139);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = l_Lean_Elab_Command_getMainModule___redArg(x_8, x_142);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = lean_unbox(x_135);
x_147 = l_Lean_SourceInfo_fromRef(x_138, x_146);
lean_dec(x_138);
x_148 = lean_mk_string_unchecked("Lean", 4, 4);
x_149 = lean_mk_string_unchecked("Elab", 4, 4);
x_150 = lean_mk_string_unchecked("Command", 7, 7);
x_151 = lean_mk_string_unchecked("aux_def", 7, 7);
lean_inc(x_151);
lean_inc(x_148);
x_152 = l_Lean_Name_mkStr4(x_148, x_149, x_150, x_151);
x_153 = lean_mk_string_unchecked("null", 4, 4);
x_154 = l_Lean_Name_mkStr1(x_153);
x_155 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_156; 
x_156 = l_Array_empty(lean_box(0));
x_17 = x_145;
x_18 = x_148;
x_19 = x_147;
x_20 = x_144;
x_21 = x_154;
x_22 = x_152;
x_23 = x_136;
x_24 = x_151;
x_25 = x_141;
x_26 = x_155;
x_27 = x_156;
goto block_123;
}
else
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_1, 0);
lean_inc(x_157);
lean_dec(x_1);
x_158 = l_Array_mkArray1___redArg(x_157);
x_17 = x_145;
x_18 = x_148;
x_19 = x_147;
x_20 = x_144;
x_21 = x_154;
x_22 = x_152;
x_23 = x_136;
x_24 = x_151;
x_25 = x_141;
x_26 = x_155;
x_27 = x_158;
goto block_123;
}
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_184 = lean_ctor_get(x_131, 1);
lean_inc(x_184);
lean_dec(x_131);
x_185 = lean_box(0);
x_210 = lean_unbox(x_185);
x_211 = l_Lean_SourceInfo_fromRef(x_125, x_210);
lean_dec(x_125);
x_212 = lean_mk_string_unchecked("Lean", 4, 4);
x_213 = lean_mk_string_unchecked("Parser", 6, 6);
x_214 = lean_mk_string_unchecked("Term", 4, 4);
x_215 = lean_mk_string_unchecked("attrInstance", 12, 12);
lean_inc(x_213);
lean_inc(x_212);
x_216 = l_Lean_Name_mkStr4(x_212, x_213, x_214, x_215);
x_217 = lean_box(0);
lean_inc(x_216);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
x_219 = lean_mk_string_unchecked("Attr", 4, 4);
x_220 = lean_mk_string_unchecked("macro", 5, 5);
lean_inc(x_220);
x_221 = l_Lean_Name_mkStr4(x_212, x_213, x_219, x_220);
lean_inc(x_211);
lean_ctor_set_tag(x_127, 2);
lean_ctor_set(x_127, 1, x_220);
lean_ctor_set(x_127, 0, x_211);
lean_inc(x_5);
x_222 = lean_mk_syntax_ident(x_5);
lean_inc(x_211);
x_223 = l_Lean_Syntax_node2(x_211, x_221, x_127, x_222);
x_224 = l_Lean_Syntax_node2(x_211, x_216, x_3, x_223);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_225 = lean_mk_string_unchecked(",", 1, 1);
x_226 = lean_unsigned_to_nat(1u);
x_227 = lean_mk_empty_array_with_capacity(x_226);
x_228 = lean_array_push(x_227, x_224);
x_229 = l_Lean_Syntax_TSepArray_ofElems(x_218, x_225, x_228);
lean_dec(x_228);
lean_dec(x_218);
x_186 = x_229;
goto block_209;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_230 = lean_ctor_get(x_2, 0);
x_231 = lean_mk_string_unchecked(",", 1, 1);
x_232 = l_Lean_Syntax_TSepArray_getElems___redArg(x_230);
x_233 = lean_array_push(x_232, x_224);
x_234 = l_Lean_Syntax_TSepArray_ofElems(x_218, x_231, x_233);
lean_dec(x_233);
lean_dec(x_218);
x_186 = x_234;
goto block_209;
}
block_209:
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_187 = l_Lean_Elab_Command_getRef(x_7, x_8, x_184);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = l_Lean_Elab_Command_getCurrMacroScope(x_7, x_8, x_189);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = l_Lean_Elab_Command_getMainModule___redArg(x_8, x_192);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_196 = lean_unbox(x_185);
x_197 = l_Lean_SourceInfo_fromRef(x_188, x_196);
lean_dec(x_188);
x_198 = lean_mk_string_unchecked("Lean", 4, 4);
x_199 = lean_mk_string_unchecked("Elab", 4, 4);
x_200 = lean_mk_string_unchecked("Command", 7, 7);
x_201 = lean_mk_string_unchecked("aux_def", 7, 7);
lean_inc(x_201);
lean_inc(x_198);
x_202 = l_Lean_Name_mkStr4(x_198, x_199, x_200, x_201);
x_203 = lean_mk_string_unchecked("null", 4, 4);
x_204 = l_Lean_Name_mkStr1(x_203);
x_205 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_206; 
x_206 = l_Array_empty(lean_box(0));
x_17 = x_195;
x_18 = x_198;
x_19 = x_197;
x_20 = x_194;
x_21 = x_204;
x_22 = x_202;
x_23 = x_186;
x_24 = x_201;
x_25 = x_191;
x_26 = x_205;
x_27 = x_206;
goto block_123;
}
else
{
lean_object* x_207; lean_object* x_208; 
x_207 = lean_ctor_get(x_1, 0);
lean_inc(x_207);
lean_dec(x_1);
x_208 = l_Array_mkArray1___redArg(x_207);
x_17 = x_195;
x_18 = x_198;
x_19 = x_197;
x_20 = x_194;
x_21 = x_204;
x_22 = x_202;
x_23 = x_186;
x_24 = x_201;
x_25 = x_191;
x_26 = x_205;
x_27 = x_208;
goto block_123;
}
}
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_235 = lean_ctor_get(x_127, 1);
lean_inc(x_235);
lean_dec(x_127);
x_236 = l_Lean_Elab_Command_getMainModule___redArg(x_8, x_235);
x_237 = lean_ctor_get(x_236, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_238 = x_236;
} else {
 lean_dec_ref(x_236);
 x_238 = lean_box(0);
}
x_239 = lean_box(0);
x_264 = lean_unbox(x_239);
x_265 = l_Lean_SourceInfo_fromRef(x_125, x_264);
lean_dec(x_125);
x_266 = lean_mk_string_unchecked("Lean", 4, 4);
x_267 = lean_mk_string_unchecked("Parser", 6, 6);
x_268 = lean_mk_string_unchecked("Term", 4, 4);
x_269 = lean_mk_string_unchecked("attrInstance", 12, 12);
lean_inc(x_267);
lean_inc(x_266);
x_270 = l_Lean_Name_mkStr4(x_266, x_267, x_268, x_269);
x_271 = lean_box(0);
lean_inc(x_270);
if (lean_is_scalar(x_238)) {
 x_272 = lean_alloc_ctor(1, 2, 0);
} else {
 x_272 = x_238;
 lean_ctor_set_tag(x_272, 1);
}
lean_ctor_set(x_272, 0, x_270);
lean_ctor_set(x_272, 1, x_271);
x_273 = lean_mk_string_unchecked("Attr", 4, 4);
x_274 = lean_mk_string_unchecked("macro", 5, 5);
lean_inc(x_274);
x_275 = l_Lean_Name_mkStr4(x_266, x_267, x_273, x_274);
lean_inc(x_265);
x_276 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_276, 0, x_265);
lean_ctor_set(x_276, 1, x_274);
lean_inc(x_5);
x_277 = lean_mk_syntax_ident(x_5);
lean_inc(x_265);
x_278 = l_Lean_Syntax_node2(x_265, x_275, x_276, x_277);
x_279 = l_Lean_Syntax_node2(x_265, x_270, x_3, x_278);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_280 = lean_mk_string_unchecked(",", 1, 1);
x_281 = lean_unsigned_to_nat(1u);
x_282 = lean_mk_empty_array_with_capacity(x_281);
x_283 = lean_array_push(x_282, x_279);
x_284 = l_Lean_Syntax_TSepArray_ofElems(x_272, x_280, x_283);
lean_dec(x_283);
lean_dec(x_272);
x_240 = x_284;
goto block_263;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_285 = lean_ctor_get(x_2, 0);
x_286 = lean_mk_string_unchecked(",", 1, 1);
x_287 = l_Lean_Syntax_TSepArray_getElems___redArg(x_285);
x_288 = lean_array_push(x_287, x_279);
x_289 = l_Lean_Syntax_TSepArray_ofElems(x_272, x_286, x_288);
lean_dec(x_288);
lean_dec(x_272);
x_240 = x_289;
goto block_263;
}
block_263:
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_241 = l_Lean_Elab_Command_getRef(x_7, x_8, x_237);
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_244 = l_Lean_Elab_Command_getCurrMacroScope(x_7, x_8, x_243);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_247 = l_Lean_Elab_Command_getMainModule___redArg(x_8, x_246);
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec(x_247);
x_250 = lean_unbox(x_239);
x_251 = l_Lean_SourceInfo_fromRef(x_242, x_250);
lean_dec(x_242);
x_252 = lean_mk_string_unchecked("Lean", 4, 4);
x_253 = lean_mk_string_unchecked("Elab", 4, 4);
x_254 = lean_mk_string_unchecked("Command", 7, 7);
x_255 = lean_mk_string_unchecked("aux_def", 7, 7);
lean_inc(x_255);
lean_inc(x_252);
x_256 = l_Lean_Name_mkStr4(x_252, x_253, x_254, x_255);
x_257 = lean_mk_string_unchecked("null", 4, 4);
x_258 = l_Lean_Name_mkStr1(x_257);
x_259 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_260; 
x_260 = l_Array_empty(lean_box(0));
x_17 = x_249;
x_18 = x_252;
x_19 = x_251;
x_20 = x_248;
x_21 = x_258;
x_22 = x_256;
x_23 = x_240;
x_24 = x_255;
x_25 = x_245;
x_26 = x_259;
x_27 = x_260;
goto block_123;
}
else
{
lean_object* x_261; lean_object* x_262; 
x_261 = lean_ctor_get(x_1, 0);
lean_inc(x_261);
lean_dec(x_1);
x_262 = l_Array_mkArray1___redArg(x_261);
x_17 = x_249;
x_18 = x_252;
x_19 = x_251;
x_20 = x_248;
x_21 = x_258;
x_22 = x_256;
x_23 = x_240;
x_24 = x_255;
x_25 = x_245;
x_26 = x_259;
x_27 = x_262;
goto block_123;
}
}
}
block_123:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_inc(x_26);
x_28 = l_Array_append(lean_box(0), x_26, x_27);
lean_dec(x_27);
lean_inc(x_21);
lean_inc(x_19);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_21);
lean_ctor_set(x_29, 2, x_28);
x_30 = lean_mk_string_unchecked("Parser", 6, 6);
x_31 = lean_mk_string_unchecked("Term", 4, 4);
x_32 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_18);
x_33 = l_Lean_Name_mkStr4(x_18, x_30, x_31, x_32);
x_34 = lean_mk_string_unchecked("@[", 2, 2);
lean_inc(x_19);
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_19);
lean_ctor_set(x_35, 1, x_34);
lean_inc(x_26);
x_36 = l_Array_append(lean_box(0), x_26, x_23);
lean_dec(x_23);
lean_inc(x_21);
lean_inc(x_19);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_19);
lean_ctor_set(x_37, 1, x_21);
lean_ctor_set(x_37, 2, x_36);
x_38 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_19);
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_19);
lean_ctor_set(x_39, 1, x_38);
lean_inc(x_19);
x_40 = l_Lean_Syntax_node3(x_19, x_33, x_35, x_37, x_39);
lean_inc(x_21);
lean_inc(x_19);
x_41 = l_Lean_Syntax_node1(x_19, x_21, x_40);
lean_inc(x_19);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_19);
lean_ctor_set(x_42, 1, x_24);
x_43 = lean_mk_string_unchecked("macroRules", 10, 10);
lean_inc(x_43);
x_44 = l_String_toSubstring_x27(x_43);
x_45 = l_Lean_Name_mkStr1(x_43);
lean_inc(x_25);
lean_inc(x_20);
x_46 = l_Lean_addMacroScope(x_20, x_45, x_25);
x_47 = lean_box(0);
lean_inc(x_19);
x_48 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_48, 0, x_19);
lean_ctor_set(x_48, 1, x_44);
lean_ctor_set(x_48, 2, x_46);
lean_ctor_set(x_48, 3, x_47);
x_49 = lean_box(1);
x_50 = lean_unbox(x_49);
x_51 = l_Lean_mkIdentFrom(x_4, x_5, x_50);
lean_inc(x_21);
lean_inc(x_19);
x_52 = l_Lean_Syntax_node2(x_19, x_21, x_48, x_51);
x_53 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_19);
x_54 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_54, 0, x_19);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_mk_string_unchecked("Macro", 5, 5);
lean_inc(x_55);
x_56 = l_String_toSubstring_x27(x_55);
lean_inc(x_55);
x_57 = l_Lean_Name_mkStr1(x_55);
lean_inc(x_25);
lean_inc(x_20);
x_58 = l_Lean_addMacroScope(x_20, x_57, x_25);
lean_inc(x_55);
lean_inc(x_18);
x_59 = l_Lean_Name_mkStr2(x_18, x_55);
x_60 = lean_box(0);
lean_inc(x_59);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_59);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_47);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_63);
lean_inc(x_19);
x_65 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_65, 0, x_19);
lean_ctor_set(x_65, 1, x_56);
lean_ctor_set(x_65, 2, x_58);
lean_ctor_set(x_65, 3, x_64);
x_66 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_19);
x_67 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_67, 0, x_19);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_mk_string_unchecked("fun", 3, 3);
lean_inc(x_68);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_18);
x_69 = l_Lean_Name_mkStr4(x_18, x_30, x_31, x_68);
lean_inc(x_19);
x_70 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_70, 0, x_19);
lean_ctor_set(x_70, 1, x_68);
x_71 = lean_mk_string_unchecked("matchAlts", 9, 9);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_18);
x_72 = l_Lean_Name_mkStr4(x_18, x_30, x_31, x_71);
x_73 = lean_mk_string_unchecked("matchAlt", 8, 8);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_18);
x_74 = l_Lean_Name_mkStr4(x_18, x_30, x_31, x_73);
x_75 = l_Array_append(lean_box(0), x_26, x_14);
lean_dec(x_14);
x_76 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_19);
x_77 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_77, 0, x_19);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_mk_string_unchecked("hole", 4, 4);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_18);
x_79 = l_Lean_Name_mkStr4(x_18, x_30, x_31, x_78);
x_80 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_19);
x_81 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_81, 0, x_19);
lean_ctor_set(x_81, 1, x_80);
lean_inc(x_19);
x_82 = l_Lean_Syntax_node1(x_19, x_79, x_81);
lean_inc(x_21);
lean_inc(x_19);
x_83 = l_Lean_Syntax_node1(x_19, x_21, x_82);
lean_inc(x_21);
lean_inc(x_19);
x_84 = l_Lean_Syntax_node1(x_19, x_21, x_83);
x_85 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_19);
x_86 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_86, 0, x_19);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_mk_string_unchecked("noErrorIfUnused", 15, 15);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_18);
x_88 = l_Lean_Name_mkStr4(x_18, x_30, x_31, x_87);
x_89 = lean_mk_string_unchecked("no_error_if_unused%", 19, 19);
lean_inc(x_19);
x_90 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_90, 0, x_19);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_18);
x_92 = l_Lean_Name_mkStr4(x_18, x_30, x_31, x_91);
x_93 = lean_mk_string_unchecked("throw", 5, 5);
lean_inc(x_93);
x_94 = l_String_toSubstring_x27(x_93);
lean_inc(x_93);
x_95 = l_Lean_Name_mkStr1(x_93);
lean_inc(x_25);
lean_inc(x_20);
x_96 = l_Lean_addMacroScope(x_20, x_95, x_25);
x_97 = lean_mk_string_unchecked("MonadExcept", 11, 11);
x_98 = l_Lean_Name_mkStr2(x_97, x_93);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_60);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_47);
lean_inc(x_19);
x_101 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_101, 0, x_19);
lean_ctor_set(x_101, 1, x_94);
lean_ctor_set(x_101, 2, x_96);
lean_ctor_set(x_101, 3, x_100);
x_102 = lean_mk_string_unchecked("Lean.Macro.Exception.unsupportedSyntax", 38, 38);
x_103 = l_String_toSubstring_x27(x_102);
x_104 = lean_mk_string_unchecked("Exception", 9, 9);
x_105 = lean_mk_string_unchecked("unsupportedSyntax", 17, 17);
x_106 = l_Lean_Name_mkStr4(x_18, x_55, x_104, x_105);
lean_inc(x_106);
x_107 = l_Lean_addMacroScope(x_20, x_106, x_25);
lean_inc(x_106);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_60);
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_106);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_47);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_110);
lean_inc(x_19);
x_112 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_112, 0, x_19);
lean_ctor_set(x_112, 1, x_103);
lean_ctor_set(x_112, 2, x_107);
lean_ctor_set(x_112, 3, x_111);
lean_inc(x_21);
lean_inc(x_19);
x_113 = l_Lean_Syntax_node1(x_19, x_21, x_112);
lean_inc(x_19);
x_114 = l_Lean_Syntax_node2(x_19, x_92, x_101, x_113);
lean_inc(x_19);
x_115 = l_Lean_Syntax_node2(x_19, x_88, x_90, x_114);
lean_inc(x_19);
x_116 = l_Lean_Syntax_node4(x_19, x_74, x_77, x_84, x_86, x_115);
x_117 = lean_array_push(x_75, x_116);
lean_inc(x_19);
x_118 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_118, 0, x_19);
lean_ctor_set(x_118, 1, x_21);
lean_ctor_set(x_118, 2, x_117);
lean_inc(x_19);
x_119 = l_Lean_Syntax_node1(x_19, x_72, x_118);
lean_inc(x_19);
x_120 = l_Lean_Syntax_node2(x_19, x_69, x_70, x_119);
x_121 = l_Lean_Syntax_node8(x_19, x_22, x_29, x_41, x_42, x_52, x_54, x_65, x_67, x_120);
if (lean_is_scalar(x_16)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_16;
}
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_17);
return x_122;
}
}
else
{
uint8_t x_290; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_290 = !lean_is_exclusive(x_13);
if (x_290 == 0)
{
return x_13;
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_291 = lean_ctor_get(x_13, 0);
x_292 = lean_ctor_get(x_13, 1);
lean_inc(x_292);
lean_inc(x_291);
lean_dec(x_13);
x_293 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_293, 0, x_291);
lean_ctor_set(x_293, 1, x_292);
return x_293;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabMacroRulesAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabMacroRulesAux_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabMacroRulesAux_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabMacroRulesAux_spec__1(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRulesAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Command_elabMacroRulesAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_43; lean_object* x_44; lean_object* x_61; 
x_15 = l_Lean_Elab_Command_getRef(x_12, x_13, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
x_19 = l_Lean_Elab_Command_getCurrMacroScope(x_12, x_13, x_17);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_21 = x_19;
} else {
 lean_dec_ref(x_19);
 x_21 = lean_box(0);
}
x_22 = l_Lean_Elab_Command_getMainModule___redArg(x_13, x_20);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_24 = x_22;
} else {
 lean_dec_ref(x_22);
 x_24 = lean_box(0);
}
x_25 = lean_box(0);
x_26 = lean_unbox(x_25);
x_27 = l_Lean_SourceInfo_fromRef(x_16, x_26);
lean_dec(x_16);
x_28 = lean_mk_string_unchecked("null", 4, 4);
x_29 = l_Lean_Name_mkStr1(x_28);
x_30 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_77; 
x_77 = l_Array_empty(lean_box(0));
x_61 = x_77;
goto block_76;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_9, 0);
lean_inc(x_78);
lean_dec(x_9);
x_79 = l_Array_mkArray1___redArg(x_78);
x_61 = x_79;
goto block_76;
}
block_42:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_inc(x_30);
x_35 = l_Array_append(lean_box(0), x_30, x_34);
lean_dec(x_34);
lean_inc(x_29);
lean_inc(x_27);
x_36 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_36, 0, x_27);
lean_ctor_set(x_36, 1, x_29);
lean_ctor_set(x_36, 2, x_35);
x_37 = l_Array_append(lean_box(0), x_30, x_11);
lean_inc(x_27);
x_38 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_38, 0, x_27);
lean_ctor_set(x_38, 1, x_29);
lean_ctor_set(x_38, 2, x_37);
lean_inc(x_27);
x_39 = l_Lean_Syntax_node1(x_27, x_1, x_38);
x_40 = l_Lean_Syntax_node6(x_27, x_2, x_33, x_31, x_3, x_32, x_36, x_39);
if (lean_is_scalar(x_24)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_24;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_23);
return x_41;
}
block_60:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_inc(x_30);
x_45 = l_Array_append(lean_box(0), x_30, x_44);
lean_dec(x_44);
lean_inc(x_29);
lean_inc(x_27);
x_46 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_46, 0, x_27);
lean_ctor_set(x_46, 1, x_29);
lean_ctor_set(x_46, 2, x_45);
lean_inc(x_27);
if (lean_is_scalar(x_21)) {
 x_47 = lean_alloc_ctor(2, 2, 0);
} else {
 x_47 = x_21;
 lean_ctor_set_tag(x_47, 2);
}
lean_ctor_set(x_47, 0, x_27);
lean_ctor_set(x_47, 1, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_48; 
lean_dec(x_18);
x_48 = l_Array_empty(lean_box(0));
x_31 = x_46;
x_32 = x_47;
x_33 = x_43;
x_34 = x_48;
goto block_42;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_49 = lean_ctor_get(x_10, 0);
lean_inc(x_49);
lean_dec(x_10);
x_50 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_27);
if (lean_is_scalar(x_18)) {
 x_51 = lean_alloc_ctor(2, 2, 0);
} else {
 x_51 = x_18;
 lean_ctor_set_tag(x_51, 2);
}
lean_ctor_set(x_51, 0, x_27);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_mk_string_unchecked("kind", 4, 4);
lean_inc(x_27);
x_53 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_53, 0, x_27);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_27);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_27);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_mk_syntax_ident(x_49);
x_57 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_27);
x_58 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_58, 0, x_27);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Array_mkArray5(lean_box(0), x_51, x_53, x_55, x_56, x_58);
x_31 = x_46;
x_32 = x_47;
x_33 = x_43;
x_34 = x_59;
goto block_42;
}
}
block_76:
{
lean_object* x_62; lean_object* x_63; 
lean_inc(x_30);
x_62 = l_Array_append(lean_box(0), x_30, x_61);
lean_dec(x_61);
lean_inc(x_29);
lean_inc(x_27);
x_63 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_63, 0, x_27);
lean_ctor_set(x_63, 1, x_29);
lean_ctor_set(x_63, 2, x_62);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_64; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_64 = l_Array_empty(lean_box(0));
x_43 = x_63;
x_44 = x_64;
goto block_60;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_65 = lean_ctor_get(x_5, 0);
x_66 = lean_mk_string_unchecked("attributes", 10, 10);
x_67 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_66);
x_68 = lean_mk_string_unchecked("@[", 2, 2);
lean_inc(x_27);
x_69 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_69, 0, x_27);
lean_ctor_set(x_69, 1, x_68);
lean_inc(x_30);
x_70 = l_Array_append(lean_box(0), x_30, x_65);
lean_inc(x_29);
lean_inc(x_27);
x_71 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_71, 0, x_27);
lean_ctor_set(x_71, 1, x_29);
lean_ctor_set(x_71, 2, x_70);
x_72 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_27);
x_73 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_73, 0, x_27);
lean_ctor_set(x_73, 1, x_72);
lean_inc(x_27);
x_74 = l_Lean_Syntax_node3(x_27, x_67, x_69, x_71, x_73);
x_75 = l_Array_mkArray1___redArg(x_74);
x_43 = x_63;
x_44 = x_75;
goto block_60;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("Parser", 6, 6);
x_7 = lean_mk_string_unchecked("Command", 7, 7);
x_8 = lean_mk_string_unchecked("macro_rules", 11, 11);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_9 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_8);
lean_inc(x_1);
x_10 = l_Lean_Syntax_isOfKind(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_104; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_104 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
lean_dec(x_3);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_476; uint8_t x_477; 
x_105 = lean_unsigned_to_nat(0u);
x_476 = l_Lean_Syntax_getArg(x_1, x_105);
x_477 = l_Lean_Syntax_isNone(x_476);
if (x_477 == 0)
{
lean_object* x_478; uint8_t x_479; 
x_478 = lean_unsigned_to_nat(1u);
lean_inc(x_476);
x_479 = l_Lean_Syntax_matchesNull(x_476, x_478);
if (x_479 == 0)
{
lean_object* x_480; 
lean_dec(x_476);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_480 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
lean_dec(x_3);
return x_480;
}
else
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; uint8_t x_484; 
x_481 = l_Lean_Syntax_getArg(x_476, x_105);
lean_dec(x_476);
x_482 = lean_mk_string_unchecked("docComment", 10, 10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_483 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_482);
lean_inc(x_481);
x_484 = l_Lean_Syntax_isOfKind(x_481, x_483);
lean_dec(x_483);
if (x_484 == 0)
{
lean_object* x_485; 
lean_dec(x_481);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_485 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
lean_dec(x_3);
return x_485;
}
else
{
lean_object* x_486; 
x_486 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_486, 0, x_481);
x_456 = x_486;
x_457 = x_2;
x_458 = x_3;
x_459 = x_4;
goto block_475;
}
}
}
else
{
lean_object* x_487; 
lean_dec(x_476);
x_487 = lean_box(0);
x_456 = x_487;
x_457 = x_2;
x_458 = x_3;
x_459 = x_4;
goto block_475;
}
block_455:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_112 = lean_unsigned_to_nat(2u);
x_113 = l_Lean_Syntax_getArg(x_1, x_112);
x_114 = lean_mk_string_unchecked("Term", 4, 4);
x_115 = lean_mk_string_unchecked("attrKind", 8, 8);
lean_inc(x_114);
lean_inc(x_6);
lean_inc(x_5);
x_116 = l_Lean_Name_mkStr4(x_5, x_6, x_114, x_115);
lean_inc(x_113);
x_117 = l_Lean_Syntax_isOfKind(x_113, x_116);
lean_dec(x_116);
if (x_117 == 0)
{
lean_object* x_118; 
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_107);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_118 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_109, x_106, x_108);
lean_dec(x_106);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_119 = lean_unsigned_to_nat(3u);
x_120 = lean_unsigned_to_nat(4u);
x_121 = l_Lean_Syntax_getArg(x_1, x_120);
lean_inc(x_121);
x_122 = l_Lean_Syntax_matchesNull(x_121, x_105);
if (x_122 == 0)
{
lean_object* x_123; uint8_t x_124; 
lean_dec(x_9);
lean_dec(x_8);
x_123 = lean_unsigned_to_nat(5u);
lean_inc(x_121);
x_124 = l_Lean_Syntax_matchesNull(x_121, x_123);
if (x_124 == 0)
{
lean_object* x_125; 
lean_dec(x_121);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_107);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_125 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_109, x_106, x_108);
lean_dec(x_106);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_126 = l_Lean_Syntax_getArg(x_1, x_123);
x_127 = lean_mk_string_unchecked("matchAlts", 9, 9);
lean_inc(x_114);
lean_inc(x_6);
lean_inc(x_5);
x_128 = l_Lean_Name_mkStr4(x_5, x_6, x_114, x_127);
lean_inc(x_126);
x_129 = l_Lean_Syntax_isOfKind(x_126, x_128);
lean_dec(x_128);
if (x_129 == 0)
{
lean_object* x_130; 
lean_dec(x_126);
lean_dec(x_121);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_107);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_130 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_109, x_106, x_108);
lean_dec(x_106);
return x_130;
}
else
{
lean_object* x_131; uint8_t x_132; 
x_131 = l_Lean_Syntax_getArg(x_126, x_105);
lean_dec(x_126);
lean_inc(x_131);
x_132 = l_Lean_Syntax_matchesNull(x_131, x_110);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_114);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_133 = lean_mk_string_unchecked("null", 4, 4);
x_134 = lean_mk_empty_array_with_capacity(x_112);
x_135 = l_Lean_Elab_Command_getRef(x_109, x_106, x_108);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = l_Lean_Syntax_getArgs(x_131);
lean_dec(x_131);
x_139 = l_Lean_Syntax_getArg(x_1, x_119);
lean_dec(x_1);
x_140 = l_Lean_Name_mkStr1(x_133);
x_141 = lean_box(2);
lean_inc(x_138);
lean_inc(x_140);
x_142 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_140);
lean_ctor_set(x_142, 2, x_138);
lean_inc(x_139);
x_143 = lean_array_push(x_134, x_139);
x_144 = l_Lean_Syntax_getArg(x_121, x_119);
lean_dec(x_121);
x_145 = lean_array_push(x_143, x_142);
x_146 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_146, 0, x_141);
lean_ctor_set(x_146, 1, x_140);
lean_ctor_set(x_146, 2, x_145);
x_147 = l_Lean_Syntax_getId(x_144);
lean_dec(x_144);
x_148 = l_Lean_replaceRef(x_146, x_136);
lean_dec(x_136);
lean_dec(x_146);
x_149 = lean_ctor_get(x_109, 0);
x_150 = lean_ctor_get(x_109, 1);
x_151 = lean_ctor_get(x_109, 2);
x_152 = lean_ctor_get(x_109, 3);
x_153 = lean_ctor_get(x_109, 4);
x_154 = lean_ctor_get(x_109, 5);
x_155 = lean_ctor_get(x_109, 7);
x_156 = lean_ctor_get(x_109, 8);
x_157 = lean_ctor_get_uint8(x_109, sizeof(void*)*9);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
x_158 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_158, 0, x_149);
lean_ctor_set(x_158, 1, x_150);
lean_ctor_set(x_158, 2, x_151);
lean_ctor_set(x_158, 3, x_152);
lean_ctor_set(x_158, 4, x_153);
lean_ctor_set(x_158, 5, x_154);
lean_ctor_set(x_158, 6, x_148);
lean_ctor_set(x_158, 7, x_155);
lean_ctor_set(x_158, 8, x_156);
lean_ctor_set_uint8(x_158, sizeof(void*)*9, x_157);
lean_inc(x_158);
x_159 = l_Lean_Elab_Command_resolveSyntaxKind(x_147, x_158, x_106, x_137);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = l_Lean_Elab_Command_elabMacroRulesAux(x_107, x_111, x_113, x_139, x_160, x_138, x_158, x_106, x_161);
lean_dec(x_106);
lean_dec(x_158);
lean_dec(x_139);
lean_dec(x_111);
return x_162;
}
else
{
uint8_t x_163; 
lean_dec(x_158);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_107);
lean_dec(x_106);
x_163 = !lean_is_exclusive(x_159);
if (x_163 == 0)
{
return x_159;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_159, 0);
x_165 = lean_ctor_get(x_159, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_159);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_167 = l_Lean_Syntax_getArg(x_131, x_105);
x_168 = lean_mk_string_unchecked("matchAlt", 8, 8);
lean_inc(x_114);
lean_inc(x_6);
lean_inc(x_5);
x_169 = l_Lean_Name_mkStr4(x_5, x_6, x_114, x_168);
lean_inc(x_167);
x_170 = l_Lean_Syntax_isOfKind(x_167, x_169);
lean_dec(x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_167);
lean_dec(x_114);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_171 = lean_mk_string_unchecked("null", 4, 4);
x_172 = lean_mk_empty_array_with_capacity(x_112);
x_173 = l_Lean_Elab_Command_getRef(x_109, x_106, x_108);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_176 = l_Lean_Syntax_getArgs(x_131);
lean_dec(x_131);
x_177 = l_Lean_Syntax_getArg(x_1, x_119);
lean_dec(x_1);
x_178 = l_Lean_Name_mkStr1(x_171);
x_179 = lean_box(2);
lean_inc(x_176);
lean_inc(x_178);
x_180 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_178);
lean_ctor_set(x_180, 2, x_176);
lean_inc(x_177);
x_181 = lean_array_push(x_172, x_177);
x_182 = l_Lean_Syntax_getArg(x_121, x_119);
lean_dec(x_121);
x_183 = lean_array_push(x_181, x_180);
x_184 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_184, 0, x_179);
lean_ctor_set(x_184, 1, x_178);
lean_ctor_set(x_184, 2, x_183);
x_185 = l_Lean_Syntax_getId(x_182);
lean_dec(x_182);
x_186 = l_Lean_replaceRef(x_184, x_174);
lean_dec(x_174);
lean_dec(x_184);
x_187 = lean_ctor_get(x_109, 0);
x_188 = lean_ctor_get(x_109, 1);
x_189 = lean_ctor_get(x_109, 2);
x_190 = lean_ctor_get(x_109, 3);
x_191 = lean_ctor_get(x_109, 4);
x_192 = lean_ctor_get(x_109, 5);
x_193 = lean_ctor_get(x_109, 7);
x_194 = lean_ctor_get(x_109, 8);
x_195 = lean_ctor_get_uint8(x_109, sizeof(void*)*9);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
lean_inc(x_191);
lean_inc(x_190);
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
x_196 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_196, 0, x_187);
lean_ctor_set(x_196, 1, x_188);
lean_ctor_set(x_196, 2, x_189);
lean_ctor_set(x_196, 3, x_190);
lean_ctor_set(x_196, 4, x_191);
lean_ctor_set(x_196, 5, x_192);
lean_ctor_set(x_196, 6, x_186);
lean_ctor_set(x_196, 7, x_193);
lean_ctor_set(x_196, 8, x_194);
lean_ctor_set_uint8(x_196, sizeof(void*)*9, x_195);
lean_inc(x_196);
x_197 = l_Lean_Elab_Command_resolveSyntaxKind(x_185, x_196, x_106, x_175);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
lean_dec(x_197);
x_200 = l_Lean_Elab_Command_elabMacroRulesAux(x_107, x_111, x_113, x_177, x_198, x_176, x_196, x_106, x_199);
lean_dec(x_106);
lean_dec(x_196);
lean_dec(x_177);
lean_dec(x_111);
return x_200;
}
else
{
uint8_t x_201; 
lean_dec(x_196);
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_107);
lean_dec(x_106);
x_201 = !lean_is_exclusive(x_197);
if (x_201 == 0)
{
return x_197;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_197, 0);
x_203 = lean_ctor_get(x_197, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_197);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
}
}
else
{
lean_object* x_205; uint8_t x_206; 
x_205 = l_Lean_Syntax_getArg(x_167, x_110);
lean_inc(x_205);
x_206 = l_Lean_Syntax_matchesNull(x_205, x_110);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_205);
lean_dec(x_167);
lean_dec(x_114);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_207 = lean_mk_string_unchecked("null", 4, 4);
x_208 = lean_mk_empty_array_with_capacity(x_112);
x_209 = l_Lean_Elab_Command_getRef(x_109, x_106, x_108);
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
x_212 = l_Lean_Syntax_getArgs(x_131);
lean_dec(x_131);
x_213 = l_Lean_Syntax_getArg(x_1, x_119);
lean_dec(x_1);
x_214 = l_Lean_Name_mkStr1(x_207);
x_215 = lean_box(2);
lean_inc(x_212);
lean_inc(x_214);
x_216 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_214);
lean_ctor_set(x_216, 2, x_212);
lean_inc(x_213);
x_217 = lean_array_push(x_208, x_213);
x_218 = l_Lean_Syntax_getArg(x_121, x_119);
lean_dec(x_121);
x_219 = lean_array_push(x_217, x_216);
x_220 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_220, 0, x_215);
lean_ctor_set(x_220, 1, x_214);
lean_ctor_set(x_220, 2, x_219);
x_221 = l_Lean_Syntax_getId(x_218);
lean_dec(x_218);
x_222 = l_Lean_replaceRef(x_220, x_210);
lean_dec(x_210);
lean_dec(x_220);
x_223 = lean_ctor_get(x_109, 0);
x_224 = lean_ctor_get(x_109, 1);
x_225 = lean_ctor_get(x_109, 2);
x_226 = lean_ctor_get(x_109, 3);
x_227 = lean_ctor_get(x_109, 4);
x_228 = lean_ctor_get(x_109, 5);
x_229 = lean_ctor_get(x_109, 7);
x_230 = lean_ctor_get(x_109, 8);
x_231 = lean_ctor_get_uint8(x_109, sizeof(void*)*9);
lean_inc(x_230);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
x_232 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_232, 0, x_223);
lean_ctor_set(x_232, 1, x_224);
lean_ctor_set(x_232, 2, x_225);
lean_ctor_set(x_232, 3, x_226);
lean_ctor_set(x_232, 4, x_227);
lean_ctor_set(x_232, 5, x_228);
lean_ctor_set(x_232, 6, x_222);
lean_ctor_set(x_232, 7, x_229);
lean_ctor_set(x_232, 8, x_230);
lean_ctor_set_uint8(x_232, sizeof(void*)*9, x_231);
lean_inc(x_232);
x_233 = l_Lean_Elab_Command_resolveSyntaxKind(x_221, x_232, x_106, x_211);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_236 = l_Lean_Elab_Command_elabMacroRulesAux(x_107, x_111, x_113, x_213, x_234, x_212, x_232, x_106, x_235);
lean_dec(x_106);
lean_dec(x_232);
lean_dec(x_213);
lean_dec(x_111);
return x_236;
}
else
{
uint8_t x_237; 
lean_dec(x_232);
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_107);
lean_dec(x_106);
x_237 = !lean_is_exclusive(x_233);
if (x_237 == 0)
{
return x_233;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_238 = lean_ctor_get(x_233, 0);
x_239 = lean_ctor_get(x_233, 1);
lean_inc(x_239);
lean_inc(x_238);
lean_dec(x_233);
x_240 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
return x_240;
}
}
}
else
{
lean_object* x_241; uint8_t x_242; 
x_241 = l_Lean_Syntax_getArg(x_205, x_105);
lean_dec(x_205);
lean_inc(x_241);
x_242 = l_Lean_Syntax_matchesNull(x_241, x_110);
if (x_242 == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_241);
lean_dec(x_167);
lean_dec(x_114);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_243 = lean_mk_string_unchecked("null", 4, 4);
x_244 = lean_mk_empty_array_with_capacity(x_112);
x_245 = l_Lean_Elab_Command_getRef(x_109, x_106, x_108);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
x_248 = l_Lean_Syntax_getArgs(x_131);
lean_dec(x_131);
x_249 = l_Lean_Syntax_getArg(x_1, x_119);
lean_dec(x_1);
x_250 = l_Lean_Name_mkStr1(x_243);
x_251 = lean_box(2);
lean_inc(x_248);
lean_inc(x_250);
x_252 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_250);
lean_ctor_set(x_252, 2, x_248);
lean_inc(x_249);
x_253 = lean_array_push(x_244, x_249);
x_254 = l_Lean_Syntax_getArg(x_121, x_119);
lean_dec(x_121);
x_255 = lean_array_push(x_253, x_252);
x_256 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_256, 0, x_251);
lean_ctor_set(x_256, 1, x_250);
lean_ctor_set(x_256, 2, x_255);
x_257 = l_Lean_Syntax_getId(x_254);
lean_dec(x_254);
x_258 = l_Lean_replaceRef(x_256, x_246);
lean_dec(x_246);
lean_dec(x_256);
x_259 = lean_ctor_get(x_109, 0);
x_260 = lean_ctor_get(x_109, 1);
x_261 = lean_ctor_get(x_109, 2);
x_262 = lean_ctor_get(x_109, 3);
x_263 = lean_ctor_get(x_109, 4);
x_264 = lean_ctor_get(x_109, 5);
x_265 = lean_ctor_get(x_109, 7);
x_266 = lean_ctor_get(x_109, 8);
x_267 = lean_ctor_get_uint8(x_109, sizeof(void*)*9);
lean_inc(x_266);
lean_inc(x_265);
lean_inc(x_264);
lean_inc(x_263);
lean_inc(x_262);
lean_inc(x_261);
lean_inc(x_260);
lean_inc(x_259);
x_268 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_268, 0, x_259);
lean_ctor_set(x_268, 1, x_260);
lean_ctor_set(x_268, 2, x_261);
lean_ctor_set(x_268, 3, x_262);
lean_ctor_set(x_268, 4, x_263);
lean_ctor_set(x_268, 5, x_264);
lean_ctor_set(x_268, 6, x_258);
lean_ctor_set(x_268, 7, x_265);
lean_ctor_set(x_268, 8, x_266);
lean_ctor_set_uint8(x_268, sizeof(void*)*9, x_267);
lean_inc(x_268);
x_269 = l_Lean_Elab_Command_resolveSyntaxKind(x_257, x_268, x_106, x_247);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
lean_dec(x_269);
x_272 = l_Lean_Elab_Command_elabMacroRulesAux(x_107, x_111, x_113, x_249, x_270, x_248, x_268, x_106, x_271);
lean_dec(x_106);
lean_dec(x_268);
lean_dec(x_249);
lean_dec(x_111);
return x_272;
}
else
{
uint8_t x_273; 
lean_dec(x_268);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_107);
lean_dec(x_106);
x_273 = !lean_is_exclusive(x_269);
if (x_273 == 0)
{
return x_269;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_274 = lean_ctor_get(x_269, 0);
x_275 = lean_ctor_get(x_269, 1);
lean_inc(x_275);
lean_inc(x_274);
lean_dec(x_269);
x_276 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set(x_276, 1, x_275);
return x_276;
}
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; uint8_t x_280; 
x_277 = l_Lean_Syntax_getArg(x_241, x_105);
lean_dec(x_241);
x_278 = lean_mk_string_unchecked("ident", 5, 5);
x_279 = l_Lean_Name_mkStr1(x_278);
lean_inc(x_277);
x_280 = l_Lean_Syntax_isOfKind(x_277, x_279);
lean_dec(x_279);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; lean_object* x_306; lean_object* x_307; 
lean_dec(x_277);
lean_dec(x_167);
lean_dec(x_114);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_281 = lean_mk_string_unchecked("null", 4, 4);
x_282 = lean_mk_empty_array_with_capacity(x_112);
x_283 = l_Lean_Elab_Command_getRef(x_109, x_106, x_108);
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_283, 1);
lean_inc(x_285);
lean_dec(x_283);
x_286 = l_Lean_Syntax_getArgs(x_131);
lean_dec(x_131);
x_287 = l_Lean_Syntax_getArg(x_1, x_119);
lean_dec(x_1);
x_288 = l_Lean_Name_mkStr1(x_281);
x_289 = lean_box(2);
lean_inc(x_286);
lean_inc(x_288);
x_290 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_288);
lean_ctor_set(x_290, 2, x_286);
lean_inc(x_287);
x_291 = lean_array_push(x_282, x_287);
x_292 = l_Lean_Syntax_getArg(x_121, x_119);
lean_dec(x_121);
x_293 = lean_array_push(x_291, x_290);
x_294 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_294, 0, x_289);
lean_ctor_set(x_294, 1, x_288);
lean_ctor_set(x_294, 2, x_293);
x_295 = l_Lean_Syntax_getId(x_292);
lean_dec(x_292);
x_296 = l_Lean_replaceRef(x_294, x_284);
lean_dec(x_284);
lean_dec(x_294);
x_297 = lean_ctor_get(x_109, 0);
x_298 = lean_ctor_get(x_109, 1);
x_299 = lean_ctor_get(x_109, 2);
x_300 = lean_ctor_get(x_109, 3);
x_301 = lean_ctor_get(x_109, 4);
x_302 = lean_ctor_get(x_109, 5);
x_303 = lean_ctor_get(x_109, 7);
x_304 = lean_ctor_get(x_109, 8);
x_305 = lean_ctor_get_uint8(x_109, sizeof(void*)*9);
lean_inc(x_304);
lean_inc(x_303);
lean_inc(x_302);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_299);
lean_inc(x_298);
lean_inc(x_297);
x_306 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_306, 0, x_297);
lean_ctor_set(x_306, 1, x_298);
lean_ctor_set(x_306, 2, x_299);
lean_ctor_set(x_306, 3, x_300);
lean_ctor_set(x_306, 4, x_301);
lean_ctor_set(x_306, 5, x_302);
lean_ctor_set(x_306, 6, x_296);
lean_ctor_set(x_306, 7, x_303);
lean_ctor_set(x_306, 8, x_304);
lean_ctor_set_uint8(x_306, sizeof(void*)*9, x_305);
lean_inc(x_306);
x_307 = l_Lean_Elab_Command_resolveSyntaxKind(x_295, x_306, x_106, x_285);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_307, 1);
lean_inc(x_309);
lean_dec(x_307);
x_310 = l_Lean_Elab_Command_elabMacroRulesAux(x_107, x_111, x_113, x_287, x_308, x_286, x_306, x_106, x_309);
lean_dec(x_106);
lean_dec(x_306);
lean_dec(x_287);
lean_dec(x_111);
return x_310;
}
else
{
uint8_t x_311; 
lean_dec(x_306);
lean_dec(x_287);
lean_dec(x_286);
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_107);
lean_dec(x_106);
x_311 = !lean_is_exclusive(x_307);
if (x_311 == 0)
{
return x_307;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_312 = lean_ctor_get(x_307, 0);
x_313 = lean_ctor_get(x_307, 1);
lean_inc(x_313);
lean_inc(x_312);
lean_dec(x_307);
x_314 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set(x_314, 1, x_313);
return x_314;
}
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; uint8_t x_342; 
lean_dec(x_131);
x_315 = lean_mk_empty_array_with_capacity(x_112);
x_316 = l_Lean_Elab_Command_getRef(x_109, x_106, x_108);
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_316, 1);
lean_inc(x_318);
lean_dec(x_316);
x_319 = l_Lean_Syntax_getArg(x_1, x_119);
lean_dec(x_1);
lean_inc(x_319);
x_320 = lean_array_push(x_315, x_319);
x_321 = lean_mk_string_unchecked("null", 4, 4);
x_322 = l_Lean_Syntax_getArg(x_167, x_119);
lean_dec(x_167);
lean_inc(x_322);
x_323 = lean_array_push(x_320, x_322);
x_324 = l_Lean_Name_mkStr1(x_321);
x_325 = lean_box(2);
lean_inc(x_324);
x_326 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set(x_326, 1, x_324);
lean_ctor_set(x_326, 2, x_323);
x_327 = l_Lean_replaceRef(x_326, x_317);
lean_dec(x_317);
lean_dec(x_326);
x_328 = lean_ctor_get(x_109, 0);
x_329 = lean_ctor_get(x_109, 1);
x_330 = lean_ctor_get(x_109, 2);
x_331 = lean_ctor_get(x_109, 3);
x_332 = lean_ctor_get(x_109, 4);
x_333 = lean_ctor_get(x_109, 5);
x_334 = lean_ctor_get(x_109, 7);
x_335 = lean_ctor_get(x_109, 8);
x_336 = lean_ctor_get_uint8(x_109, sizeof(void*)*9);
lean_inc(x_335);
lean_inc(x_334);
lean_inc(x_333);
lean_inc(x_332);
lean_inc(x_331);
lean_inc(x_330);
lean_inc(x_329);
lean_inc(x_328);
x_337 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_337, 0, x_328);
lean_ctor_set(x_337, 1, x_329);
lean_ctor_set(x_337, 2, x_330);
lean_ctor_set(x_337, 3, x_331);
lean_ctor_set(x_337, 4, x_332);
lean_ctor_set(x_337, 5, x_333);
lean_ctor_set(x_337, 6, x_327);
lean_ctor_set(x_337, 7, x_334);
lean_ctor_set(x_337, 8, x_335);
lean_ctor_set_uint8(x_337, sizeof(void*)*9, x_336);
x_338 = l_Lean_Elab_Command_getRef(x_337, x_106, x_318);
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_338, 1);
lean_inc(x_340);
lean_dec(x_338);
x_341 = l_Lean_Elab_Command_getCurrMacroScope(x_337, x_106, x_340);
x_342 = !lean_is_exclusive(x_341);
if (x_342 == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; 
x_343 = lean_ctor_get(x_341, 1);
x_344 = lean_ctor_get(x_341, 0);
lean_dec(x_344);
x_345 = l_Lean_Elab_Command_getMainModule___redArg(x_106, x_343);
x_346 = !lean_is_exclusive(x_345);
if (x_346 == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_347 = lean_ctor_get(x_345, 1);
x_348 = lean_ctor_get(x_345, 0);
lean_dec(x_348);
x_349 = l_Lean_Syntax_getArg(x_121, x_119);
lean_dec(x_121);
x_350 = lean_box(0);
x_351 = l_Lean_SourceInfo_fromRef(x_339, x_122);
lean_dec(x_339);
x_352 = lean_mk_string_unchecked("attrInstance", 12, 12);
lean_inc(x_114);
lean_inc(x_6);
lean_inc(x_5);
x_353 = l_Lean_Name_mkStr4(x_5, x_6, x_114, x_352);
lean_inc(x_353);
lean_ctor_set_tag(x_345, 1);
lean_ctor_set(x_345, 1, x_350);
lean_ctor_set(x_345, 0, x_353);
x_354 = lean_mk_string_unchecked("Attr", 4, 4);
x_355 = lean_mk_string_unchecked("macro", 5, 5);
lean_inc(x_355);
lean_inc(x_6);
lean_inc(x_5);
x_356 = l_Lean_Name_mkStr4(x_5, x_6, x_354, x_355);
lean_inc(x_351);
lean_ctor_set_tag(x_341, 2);
lean_ctor_set(x_341, 1, x_355);
lean_ctor_set(x_341, 0, x_351);
lean_inc(x_349);
lean_inc(x_351);
x_357 = l_Lean_Syntax_node2(x_351, x_356, x_341, x_349);
x_358 = l_Lean_Syntax_node2(x_351, x_353, x_113, x_357);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_359 = lean_mk_string_unchecked(",", 1, 1);
x_360 = lean_mk_empty_array_with_capacity(x_110);
x_361 = lean_array_push(x_360, x_358);
x_362 = l_Lean_Syntax_TSepArray_ofElems(x_345, x_359, x_361);
lean_dec(x_361);
lean_dec(x_345);
lean_inc(x_349);
x_73 = x_319;
x_74 = x_349;
x_75 = x_349;
x_76 = x_322;
x_77 = x_347;
x_78 = x_277;
x_79 = x_122;
x_80 = x_337;
x_81 = x_107;
x_82 = x_324;
x_83 = x_106;
x_84 = x_114;
x_85 = x_362;
goto block_103;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_363 = lean_ctor_get(x_111, 0);
lean_inc(x_363);
lean_dec(x_111);
x_364 = lean_mk_string_unchecked(",", 1, 1);
x_365 = l_Lean_Syntax_TSepArray_getElems___redArg(x_363);
lean_dec(x_363);
x_366 = lean_array_push(x_365, x_358);
x_367 = l_Lean_Syntax_TSepArray_ofElems(x_345, x_364, x_366);
lean_dec(x_366);
lean_dec(x_345);
lean_inc(x_349);
x_73 = x_319;
x_74 = x_349;
x_75 = x_349;
x_76 = x_322;
x_77 = x_347;
x_78 = x_277;
x_79 = x_122;
x_80 = x_337;
x_81 = x_107;
x_82 = x_324;
x_83 = x_106;
x_84 = x_114;
x_85 = x_367;
goto block_103;
}
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_368 = lean_ctor_get(x_345, 1);
lean_inc(x_368);
lean_dec(x_345);
x_369 = l_Lean_Syntax_getArg(x_121, x_119);
lean_dec(x_121);
x_370 = lean_box(0);
x_371 = l_Lean_SourceInfo_fromRef(x_339, x_122);
lean_dec(x_339);
x_372 = lean_mk_string_unchecked("attrInstance", 12, 12);
lean_inc(x_114);
lean_inc(x_6);
lean_inc(x_5);
x_373 = l_Lean_Name_mkStr4(x_5, x_6, x_114, x_372);
lean_inc(x_373);
x_374 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_374, 0, x_373);
lean_ctor_set(x_374, 1, x_370);
x_375 = lean_mk_string_unchecked("Attr", 4, 4);
x_376 = lean_mk_string_unchecked("macro", 5, 5);
lean_inc(x_376);
lean_inc(x_6);
lean_inc(x_5);
x_377 = l_Lean_Name_mkStr4(x_5, x_6, x_375, x_376);
lean_inc(x_371);
lean_ctor_set_tag(x_341, 2);
lean_ctor_set(x_341, 1, x_376);
lean_ctor_set(x_341, 0, x_371);
lean_inc(x_369);
lean_inc(x_371);
x_378 = l_Lean_Syntax_node2(x_371, x_377, x_341, x_369);
x_379 = l_Lean_Syntax_node2(x_371, x_373, x_113, x_378);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_380 = lean_mk_string_unchecked(",", 1, 1);
x_381 = lean_mk_empty_array_with_capacity(x_110);
x_382 = lean_array_push(x_381, x_379);
x_383 = l_Lean_Syntax_TSepArray_ofElems(x_374, x_380, x_382);
lean_dec(x_382);
lean_dec(x_374);
lean_inc(x_369);
x_73 = x_319;
x_74 = x_369;
x_75 = x_369;
x_76 = x_322;
x_77 = x_368;
x_78 = x_277;
x_79 = x_122;
x_80 = x_337;
x_81 = x_107;
x_82 = x_324;
x_83 = x_106;
x_84 = x_114;
x_85 = x_383;
goto block_103;
}
else
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_384 = lean_ctor_get(x_111, 0);
lean_inc(x_384);
lean_dec(x_111);
x_385 = lean_mk_string_unchecked(",", 1, 1);
x_386 = l_Lean_Syntax_TSepArray_getElems___redArg(x_384);
lean_dec(x_384);
x_387 = lean_array_push(x_386, x_379);
x_388 = l_Lean_Syntax_TSepArray_ofElems(x_374, x_385, x_387);
lean_dec(x_387);
lean_dec(x_374);
lean_inc(x_369);
x_73 = x_319;
x_74 = x_369;
x_75 = x_369;
x_76 = x_322;
x_77 = x_368;
x_78 = x_277;
x_79 = x_122;
x_80 = x_337;
x_81 = x_107;
x_82 = x_324;
x_83 = x_106;
x_84 = x_114;
x_85 = x_388;
goto block_103;
}
}
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_389 = lean_ctor_get(x_341, 1);
lean_inc(x_389);
lean_dec(x_341);
x_390 = l_Lean_Elab_Command_getMainModule___redArg(x_106, x_389);
x_391 = lean_ctor_get(x_390, 1);
lean_inc(x_391);
if (lean_is_exclusive(x_390)) {
 lean_ctor_release(x_390, 0);
 lean_ctor_release(x_390, 1);
 x_392 = x_390;
} else {
 lean_dec_ref(x_390);
 x_392 = lean_box(0);
}
x_393 = l_Lean_Syntax_getArg(x_121, x_119);
lean_dec(x_121);
x_394 = lean_box(0);
x_395 = l_Lean_SourceInfo_fromRef(x_339, x_122);
lean_dec(x_339);
x_396 = lean_mk_string_unchecked("attrInstance", 12, 12);
lean_inc(x_114);
lean_inc(x_6);
lean_inc(x_5);
x_397 = l_Lean_Name_mkStr4(x_5, x_6, x_114, x_396);
lean_inc(x_397);
if (lean_is_scalar(x_392)) {
 x_398 = lean_alloc_ctor(1, 2, 0);
} else {
 x_398 = x_392;
 lean_ctor_set_tag(x_398, 1);
}
lean_ctor_set(x_398, 0, x_397);
lean_ctor_set(x_398, 1, x_394);
x_399 = lean_mk_string_unchecked("Attr", 4, 4);
x_400 = lean_mk_string_unchecked("macro", 5, 5);
lean_inc(x_400);
lean_inc(x_6);
lean_inc(x_5);
x_401 = l_Lean_Name_mkStr4(x_5, x_6, x_399, x_400);
lean_inc(x_395);
x_402 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_402, 0, x_395);
lean_ctor_set(x_402, 1, x_400);
lean_inc(x_393);
lean_inc(x_395);
x_403 = l_Lean_Syntax_node2(x_395, x_401, x_402, x_393);
x_404 = l_Lean_Syntax_node2(x_395, x_397, x_113, x_403);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_405 = lean_mk_string_unchecked(",", 1, 1);
x_406 = lean_mk_empty_array_with_capacity(x_110);
x_407 = lean_array_push(x_406, x_404);
x_408 = l_Lean_Syntax_TSepArray_ofElems(x_398, x_405, x_407);
lean_dec(x_407);
lean_dec(x_398);
lean_inc(x_393);
x_73 = x_319;
x_74 = x_393;
x_75 = x_393;
x_76 = x_322;
x_77 = x_391;
x_78 = x_277;
x_79 = x_122;
x_80 = x_337;
x_81 = x_107;
x_82 = x_324;
x_83 = x_106;
x_84 = x_114;
x_85 = x_408;
goto block_103;
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; 
x_409 = lean_ctor_get(x_111, 0);
lean_inc(x_409);
lean_dec(x_111);
x_410 = lean_mk_string_unchecked(",", 1, 1);
x_411 = l_Lean_Syntax_TSepArray_getElems___redArg(x_409);
lean_dec(x_409);
x_412 = lean_array_push(x_411, x_404);
x_413 = l_Lean_Syntax_TSepArray_ofElems(x_398, x_410, x_412);
lean_dec(x_412);
lean_dec(x_398);
lean_inc(x_393);
x_73 = x_319;
x_74 = x_393;
x_75 = x_393;
x_76 = x_322;
x_77 = x_391;
x_78 = x_277;
x_79 = x_122;
x_80 = x_337;
x_81 = x_107;
x_82 = x_324;
x_83 = x_106;
x_84 = x_114;
x_85 = x_413;
goto block_103;
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; 
lean_dec(x_121);
lean_dec(x_7);
x_414 = lean_unsigned_to_nat(5u);
x_415 = l_Lean_Syntax_getArg(x_1, x_414);
x_416 = lean_mk_string_unchecked("matchAlts", 9, 9);
lean_inc(x_114);
lean_inc(x_6);
lean_inc(x_5);
x_417 = l_Lean_Name_mkStr4(x_5, x_6, x_114, x_416);
lean_inc(x_415);
x_418 = l_Lean_Syntax_isOfKind(x_415, x_417);
if (x_418 == 0)
{
lean_object* x_419; 
lean_dec(x_417);
lean_dec(x_415);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_107);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_419 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_109, x_106, x_108);
lean_dec(x_106);
return x_419;
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; uint8_t x_444; lean_object* x_445; lean_object* x_446; 
x_420 = l_Lean_Syntax_getArg(x_415, x_105);
lean_dec(x_415);
x_421 = l_Lean_Syntax_getArg(x_1, x_119);
lean_dec(x_1);
x_422 = lean_mk_string_unchecked("null", 4, 4);
x_423 = lean_mk_empty_array_with_capacity(x_112);
x_424 = l_Lean_Elab_Command_getRef(x_109, x_106, x_108);
x_425 = lean_ctor_get(x_424, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_424, 1);
lean_inc(x_426);
lean_dec(x_424);
x_427 = l_Lean_Syntax_getArgs(x_420);
lean_dec(x_420);
x_428 = l_Lean_Name_mkStr1(x_422);
x_429 = lean_box(2);
lean_inc(x_427);
lean_inc(x_428);
x_430 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_430, 0, x_429);
lean_ctor_set(x_430, 1, x_428);
lean_ctor_set(x_430, 2, x_427);
x_431 = lean_array_push(x_423, x_421);
lean_inc(x_8);
x_432 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 14, 9);
lean_closure_set(x_432, 0, x_417);
lean_closure_set(x_432, 1, x_9);
lean_closure_set(x_432, 2, x_113);
lean_closure_set(x_432, 3, x_8);
lean_closure_set(x_432, 4, x_111);
lean_closure_set(x_432, 5, x_5);
lean_closure_set(x_432, 6, x_6);
lean_closure_set(x_432, 7, x_114);
lean_closure_set(x_432, 8, x_107);
x_433 = lean_array_push(x_431, x_430);
x_434 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_434, 0, x_429);
lean_ctor_set(x_434, 1, x_428);
lean_ctor_set(x_434, 2, x_433);
x_435 = l_Lean_replaceRef(x_434, x_425);
lean_dec(x_425);
lean_dec(x_434);
x_436 = lean_ctor_get(x_109, 0);
x_437 = lean_ctor_get(x_109, 1);
x_438 = lean_ctor_get(x_109, 2);
x_439 = lean_ctor_get(x_109, 3);
x_440 = lean_ctor_get(x_109, 4);
x_441 = lean_ctor_get(x_109, 5);
x_442 = lean_ctor_get(x_109, 7);
x_443 = lean_ctor_get(x_109, 8);
x_444 = lean_ctor_get_uint8(x_109, sizeof(void*)*9);
lean_inc(x_443);
lean_inc(x_442);
lean_inc(x_441);
lean_inc(x_440);
lean_inc(x_439);
lean_inc(x_438);
lean_inc(x_437);
lean_inc(x_436);
x_445 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_445, 0, x_436);
lean_ctor_set(x_445, 1, x_437);
lean_ctor_set(x_445, 2, x_438);
lean_ctor_set(x_445, 3, x_439);
lean_ctor_set(x_445, 4, x_440);
lean_ctor_set(x_445, 5, x_441);
lean_ctor_set(x_445, 6, x_435);
lean_ctor_set(x_445, 7, x_442);
lean_ctor_set(x_445, 8, x_443);
lean_ctor_set_uint8(x_445, sizeof(void*)*9, x_444);
x_446 = l_Lean_Elab_Command_expandNoKindMacroRulesAux(x_427, x_8, x_432, x_445, x_106, x_426);
lean_dec(x_8);
lean_dec(x_427);
if (lean_obj_tag(x_446) == 0)
{
uint8_t x_447; 
x_447 = !lean_is_exclusive(x_446);
if (x_447 == 0)
{
return x_446;
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_448 = lean_ctor_get(x_446, 0);
x_449 = lean_ctor_get(x_446, 1);
lean_inc(x_449);
lean_inc(x_448);
lean_dec(x_446);
x_450 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_450, 0, x_448);
lean_ctor_set(x_450, 1, x_449);
return x_450;
}
}
else
{
uint8_t x_451; 
x_451 = !lean_is_exclusive(x_446);
if (x_451 == 0)
{
return x_446;
}
else
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_452 = lean_ctor_get(x_446, 0);
x_453 = lean_ctor_get(x_446, 1);
lean_inc(x_453);
lean_inc(x_452);
lean_dec(x_446);
x_454 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_454, 0, x_452);
lean_ctor_set(x_454, 1, x_453);
return x_454;
}
}
}
}
}
}
block_475:
{
lean_object* x_460; lean_object* x_461; uint8_t x_462; 
x_460 = lean_unsigned_to_nat(1u);
x_461 = l_Lean_Syntax_getArg(x_1, x_460);
x_462 = l_Lean_Syntax_isNone(x_461);
if (x_462 == 0)
{
uint8_t x_463; 
lean_inc(x_461);
x_463 = l_Lean_Syntax_matchesNull(x_461, x_460);
if (x_463 == 0)
{
lean_object* x_464; 
lean_dec(x_461);
lean_dec(x_456);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_464 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_457, x_458, x_459);
lean_dec(x_458);
return x_464;
}
else
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; uint8_t x_469; 
x_465 = l_Lean_Syntax_getArg(x_461, x_105);
lean_dec(x_461);
x_466 = lean_mk_string_unchecked("Term", 4, 4);
x_467 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
x_468 = l_Lean_Name_mkStr4(x_5, x_6, x_466, x_467);
lean_inc(x_465);
x_469 = l_Lean_Syntax_isOfKind(x_465, x_468);
lean_dec(x_468);
if (x_469 == 0)
{
lean_object* x_470; 
lean_dec(x_465);
lean_dec(x_456);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_470 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_457, x_458, x_459);
lean_dec(x_458);
return x_470;
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_471 = l_Lean_Syntax_getArg(x_465, x_460);
lean_dec(x_465);
x_472 = l_Lean_Syntax_getArgs(x_471);
lean_dec(x_471);
x_473 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_473, 0, x_472);
x_106 = x_458;
x_107 = x_456;
x_108 = x_459;
x_109 = x_457;
x_110 = x_460;
x_111 = x_473;
goto block_455;
}
}
}
else
{
lean_object* x_474; 
lean_dec(x_461);
x_474 = lean_box(0);
x_106 = x_458;
x_107 = x_456;
x_108 = x_459;
x_109 = x_457;
x_110 = x_460;
x_111 = x_474;
goto block_455;
}
}
}
block_72:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_inc(x_19);
x_27 = l_Array_append(lean_box(0), x_19, x_26);
lean_dec(x_26);
lean_inc(x_24);
lean_inc(x_14);
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_14);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_18);
lean_inc(x_6);
lean_inc(x_5);
x_30 = l_Lean_Name_mkStr4(x_5, x_6, x_18, x_29);
x_31 = lean_mk_string_unchecked("@[", 2, 2);
lean_inc(x_14);
x_32 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_32, 0, x_14);
lean_ctor_set(x_32, 1, x_31);
lean_inc(x_19);
x_33 = l_Array_append(lean_box(0), x_19, x_25);
lean_dec(x_25);
lean_inc(x_24);
lean_inc(x_14);
x_34 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_34, 0, x_14);
lean_ctor_set(x_34, 1, x_24);
lean_ctor_set(x_34, 2, x_33);
x_35 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_14);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_14);
lean_ctor_set(x_36, 1, x_35);
lean_inc(x_14);
x_37 = l_Lean_Syntax_node3(x_14, x_30, x_32, x_34, x_36);
lean_inc(x_24);
lean_inc(x_14);
x_38 = l_Lean_Syntax_node1(x_14, x_24, x_37);
lean_inc(x_14);
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_14);
lean_ctor_set(x_39, 1, x_15);
x_40 = l_Lean_Syntax_getId(x_12);
lean_dec(x_12);
x_41 = l_Lean_mkIdentFrom(x_11, x_40, x_10);
lean_dec(x_11);
lean_inc(x_24);
lean_inc(x_14);
x_42 = l_Lean_Syntax_node2(x_14, x_24, x_41, x_21);
x_43 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_14);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_14);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_mk_string_unchecked("Macro", 5, 5);
lean_inc(x_45);
x_46 = l_String_toSubstring_x27(x_45);
lean_inc(x_45);
x_47 = l_Lean_Name_mkStr1(x_45);
x_48 = l_Lean_addMacroScope(x_13, x_47, x_17);
lean_inc(x_5);
x_49 = l_Lean_Name_mkStr2(x_5, x_45);
x_50 = lean_box(0);
lean_inc(x_49);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_49);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_51);
lean_ctor_set(x_55, 1, x_54);
lean_inc(x_14);
x_56 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_56, 0, x_14);
lean_ctor_set(x_56, 1, x_46);
lean_ctor_set(x_56, 2, x_48);
lean_ctor_set(x_56, 3, x_55);
x_57 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_14);
x_58 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_58, 0, x_14);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_mk_string_unchecked("fun", 3, 3);
lean_inc(x_59);
lean_inc(x_18);
lean_inc(x_6);
lean_inc(x_5);
x_60 = l_Lean_Name_mkStr4(x_5, x_6, x_18, x_59);
lean_inc(x_14);
x_61 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_61, 0, x_14);
lean_ctor_set(x_61, 1, x_59);
x_62 = lean_mk_string_unchecked("basicFun", 8, 8);
x_63 = l_Lean_Name_mkStr4(x_5, x_6, x_18, x_62);
lean_inc(x_24);
lean_inc(x_14);
x_64 = l_Lean_Syntax_node1(x_14, x_24, x_23);
lean_inc(x_14);
x_65 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_65, 0, x_14);
lean_ctor_set(x_65, 1, x_24);
lean_ctor_set(x_65, 2, x_19);
x_66 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_14);
x_67 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_67, 0, x_14);
lean_ctor_set(x_67, 1, x_66);
lean_inc(x_14);
x_68 = l_Lean_Syntax_node4(x_14, x_63, x_64, x_65, x_67, x_22);
lean_inc(x_14);
x_69 = l_Lean_Syntax_node2(x_14, x_60, x_61, x_68);
x_70 = l_Lean_Syntax_node8(x_14, x_16, x_28, x_38, x_39, x_42, x_44, x_56, x_58, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_20);
return x_71;
}
block_103:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_86 = l_Lean_Elab_Command_getRef(x_80, x_83, x_77);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = l_Lean_Elab_Command_getCurrMacroScope(x_80, x_83, x_88);
lean_dec(x_80);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = l_Lean_Elab_Command_getMainModule___redArg(x_83, x_91);
lean_dec(x_83);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = l_Lean_SourceInfo_fromRef(x_87, x_79);
lean_dec(x_87);
x_96 = lean_mk_string_unchecked("Elab", 4, 4);
x_97 = lean_mk_string_unchecked("aux_def", 7, 7);
lean_inc(x_97);
lean_inc(x_5);
x_98 = l_Lean_Name_mkStr4(x_5, x_96, x_7, x_97);
x_99 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_100; 
x_100 = l_Array_empty(lean_box(0));
x_11 = x_73;
x_12 = x_74;
x_13 = x_93;
x_14 = x_95;
x_15 = x_97;
x_16 = x_98;
x_17 = x_90;
x_18 = x_84;
x_19 = x_99;
x_20 = x_94;
x_21 = x_75;
x_22 = x_76;
x_23 = x_78;
x_24 = x_82;
x_25 = x_85;
x_26 = x_100;
goto block_72;
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_81, 0);
lean_inc(x_101);
lean_dec(x_81);
x_102 = l_Array_mkArray1___redArg(x_101);
x_11 = x_73;
x_12 = x_74;
x_13 = x_93;
x_14 = x_95;
x_15 = x_97;
x_16 = x_98;
x_17 = x_90;
x_18 = x_84;
x_19 = x_99;
x_20 = x_94;
x_21 = x_75;
x_22 = x_76;
x_23 = x_78;
x_24 = x_82;
x_25 = x_85;
x_26 = x_102;
goto block_72;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__1___boxed), 4, 0);
x_6 = l_Lean_Elab_Command_adaptExpander(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Command_elabMacroRules___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabMacroRules___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabMacroRules__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Command", 7, 7);
x_6 = lean_mk_string_unchecked("macro_rules", 11, 11);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("elabMacroRules", 14, 14);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules), 4, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Command", 7, 7);
x_5 = lean_mk_string_unchecked("elabMacroRules", 14, 14);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(50u);
x_8 = lean_unsigned_to_nat(38u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(68u);
x_11 = lean_unsigned_to_nat(32u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(42u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(56u);
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
lean_object* initialize_Lean_Elab_Syntax(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_AuxDef(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_MacroRules(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_AuxDef(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabMacroRules__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
