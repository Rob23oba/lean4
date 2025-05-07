// Lean compiler output
// Module: Lean.Elab.ElabRules
// Imports: Lean.Elab.MacroArgUtil Lean.Elab.AuxDef
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
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_Command_mkNameFromParserSyntax___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getQuotContent(lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabElab_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(size_t, size_t, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabElabRulesAux_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Elab_Command_elabElabRulesAux_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Array_mkArray2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Array_unzip___redArg(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabElab_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandNoKindMacroRulesAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_evalOptPrio___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabElabRulesAux_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Elab_Command_elabElabRulesAux_spec__2_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_resolveSyntaxKind(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabElabRules__1(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_ofElems(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addMacroScopeIfLocal___at___Lean_Elab_Command_elabSyntax_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isQuot(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabElabRulesAux_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_adaptExpander(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Command_checkRuleKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Elab_Command_getMainModule___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabElabRulesAux_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_____private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Syntax_node8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
extern lean_object* l_Lean_instInhabitedSyntax;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabElab_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___Lean_Elab_Command_elabElabRulesAux_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__1(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabElab__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___Lean_Elab_Command_elabElabRulesAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
lean_object* l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandMacroArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___Lean_Elab_Command_elabElabRulesAux_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Elab_Command_getRef(x_3, x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = l_Lean_mkIdentFrom(x_8, x_1, x_2);
lean_dec(x_8);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
x_12 = l_Lean_mkIdentFrom(x_10, x_1, x_2);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabElabRulesAux_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Elab_Command_elabElabRulesAux_spec__2_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_66 = lean_mk_string_unchecked("invalid elab_rules alternative, unexpected syntax node kind '", 61, 61);
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
x_80 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabElabRulesAux_spec__1(x_1, x_74, x_78, x_79, x_77);
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
x_28 = x_57;
x_29 = x_59;
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
x_28 = x_57;
x_29 = x_59;
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
x_30 = lean_mk_string_unchecked("invalid elab_rules alternative, expected syntax node kind '", 59, 59);
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
x_37 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_26, x_36, x_28, x_27, x_29);
lean_dec(x_26);
x_20 = x_37;
goto block_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabElabRulesAux_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_66 = lean_mk_string_unchecked("invalid elab_rules alternative, unexpected syntax node kind '", 61, 61);
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
x_80 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabElabRulesAux_spec__1(x_1, x_74, x_78, x_79, x_77);
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
x_28 = x_58;
x_29 = x_59;
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
x_28 = x_58;
x_29 = x_59;
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
x_18 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Elab_Command_elabElabRulesAux_spec__2_spec__2(x_1, x_2, x_16, x_17, x_5, x_6, x_13);
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
x_30 = lean_mk_string_unchecked("invalid elab_rules alternative, expected syntax node kind '", 59, 59);
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
x_37 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_26, x_36, x_27, x_28, x_29);
lean_dec(x_26);
x_20 = x_37;
goto block_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
x_10 = l_Lean_mkIdentFromRef___at___Lean_Elab_Command_elabElabRulesAux_spec__0(x_1, x_9, x_5, x_6, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Command_getRef(x_5, x_6, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Elab_Command_getCurrMacroScope(x_5, x_6, x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Elab_Command_getMainModule___redArg(x_6, x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = lean_unbox(x_8);
x_22 = l_Lean_SourceInfo_fromRef(x_14, x_21);
lean_dec(x_14);
x_23 = lean_mk_string_unchecked("Lean", 4, 4);
x_24 = lean_mk_string_unchecked("Parser", 6, 6);
x_25 = lean_mk_string_unchecked("Term", 4, 4);
x_26 = lean_mk_string_unchecked("attrInstance", 12, 12);
lean_inc(x_24);
lean_inc(x_23);
x_27 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_26);
x_28 = lean_mk_string_unchecked("Attr", 4, 4);
x_29 = lean_mk_string_unchecked("simple", 6, 6);
x_30 = l_Lean_Name_mkStr4(x_23, x_24, x_28, x_29);
x_31 = lean_mk_syntax_ident(x_4);
x_32 = lean_mk_string_unchecked("null", 4, 4);
x_33 = l_Lean_Name_mkStr1(x_32);
lean_inc(x_22);
x_34 = l_Lean_Syntax_node1(x_22, x_33, x_11);
lean_inc(x_22);
x_35 = l_Lean_Syntax_node2(x_22, x_30, x_31, x_34);
x_36 = l_Lean_Syntax_node2(x_22, x_27, x_2, x_35);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_mk_empty_array_with_capacity(x_37);
x_39 = lean_array_push(x_38, x_36);
lean_ctor_set(x_18, 0, x_39);
return x_18;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_3, 0);
x_41 = l_Lean_Syntax_TSepArray_getElems___redArg(x_40);
x_42 = lean_array_push(x_41, x_36);
lean_ctor_set(x_18, 0, x_42);
return x_18;
}
}
else
{
lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_43 = lean_ctor_get(x_18, 1);
lean_inc(x_43);
lean_dec(x_18);
x_44 = lean_unbox(x_8);
x_45 = l_Lean_SourceInfo_fromRef(x_14, x_44);
lean_dec(x_14);
x_46 = lean_mk_string_unchecked("Lean", 4, 4);
x_47 = lean_mk_string_unchecked("Parser", 6, 6);
x_48 = lean_mk_string_unchecked("Term", 4, 4);
x_49 = lean_mk_string_unchecked("attrInstance", 12, 12);
lean_inc(x_47);
lean_inc(x_46);
x_50 = l_Lean_Name_mkStr4(x_46, x_47, x_48, x_49);
x_51 = lean_mk_string_unchecked("Attr", 4, 4);
x_52 = lean_mk_string_unchecked("simple", 6, 6);
x_53 = l_Lean_Name_mkStr4(x_46, x_47, x_51, x_52);
x_54 = lean_mk_syntax_ident(x_4);
x_55 = lean_mk_string_unchecked("null", 4, 4);
x_56 = l_Lean_Name_mkStr1(x_55);
lean_inc(x_45);
x_57 = l_Lean_Syntax_node1(x_45, x_56, x_11);
lean_inc(x_45);
x_58 = l_Lean_Syntax_node2(x_45, x_53, x_54, x_57);
x_59 = l_Lean_Syntax_node2(x_45, x_50, x_2, x_58);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_mk_empty_array_with_capacity(x_60);
x_62 = lean_array_push(x_61, x_59);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_43);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_3, 0);
x_65 = l_Lean_Syntax_TSepArray_getElems___redArg(x_64);
x_66 = lean_array_push(x_65, x_59);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_43);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; lean_object* x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_array_size(x_7);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_usize_of_nat(x_12);
lean_inc(x_4);
x_14 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabElabRulesAux_spec__2(x_4, x_11, x_13, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; uint8_t x_460; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_17 = x_14;
} else {
 lean_dec_ref(x_14);
 x_17 = lean_box(0);
}
if (lean_obj_tag(x_5) == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; uint8_t x_612; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_609 = lean_mk_string_unchecked("invalid elab_rules command, specify category using `elab_rules : <cat> ...`", 75, 75);
x_610 = l_Lean_stringToMessageData(x_609);
lean_dec(x_609);
x_611 = l_Lean_throwError___at_____private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_spec__0___redArg(x_610, x_8, x_9, x_16);
x_612 = !lean_is_exclusive(x_611);
if (x_612 == 0)
{
return x_611;
}
else
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; 
x_613 = lean_ctor_get(x_611, 0);
x_614 = lean_ctor_get(x_611, 1);
lean_inc(x_614);
lean_inc(x_613);
lean_dec(x_611);
x_615 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_615, 0, x_613);
lean_ctor_set(x_615, 1, x_614);
return x_615;
}
}
else
{
lean_object* x_616; lean_object* x_617; 
x_616 = lean_mk_string_unchecked("term", 4, 4);
x_617 = l_Lean_Name_mkStr1(x_616);
x_487 = x_617;
x_488 = x_8;
x_489 = x_9;
x_490 = x_16;
goto block_608;
}
}
else
{
lean_object* x_618; lean_object* x_619; 
x_618 = lean_ctor_get(x_5, 0);
x_619 = l_Lean_Syntax_getId(x_618);
x_487 = x_619;
x_488 = x_8;
x_489 = x_9;
x_490 = x_16;
goto block_608;
}
block_152:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_inc(x_30);
x_32 = l_Array_append(lean_box(0), x_30, x_31);
lean_dec(x_31);
lean_inc(x_28);
lean_inc(x_18);
x_33 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_33, 0, x_18);
lean_ctor_set(x_33, 1, x_28);
lean_ctor_set(x_33, 2, x_32);
x_34 = lean_mk_string_unchecked("Parser", 6, 6);
x_35 = lean_mk_string_unchecked("Term", 4, 4);
x_36 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_29);
x_37 = l_Lean_Name_mkStr4(x_29, x_34, x_35, x_36);
x_38 = lean_mk_string_unchecked("@[", 2, 2);
lean_inc(x_18);
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_18);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_mk_string_unchecked("attrInstance", 12, 12);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_29);
x_41 = l_Lean_Name_mkStr4(x_29, x_34, x_35, x_40);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_25);
x_43 = lean_mk_string_unchecked(",", 1, 1);
x_44 = l_Lean_Syntax_TSepArray_ofElems(x_42, x_43, x_22);
lean_dec(x_22);
lean_dec(x_42);
lean_inc(x_30);
x_45 = l_Array_append(lean_box(0), x_30, x_44);
lean_dec(x_44);
lean_inc(x_28);
lean_inc(x_18);
x_46 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_46, 0, x_18);
lean_ctor_set(x_46, 1, x_28);
lean_ctor_set(x_46, 2, x_45);
x_47 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_18);
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_18);
lean_ctor_set(x_48, 1, x_47);
lean_inc(x_18);
x_49 = l_Lean_Syntax_node3(x_18, x_37, x_39, x_46, x_48);
lean_inc(x_28);
lean_inc(x_18);
x_50 = l_Lean_Syntax_node1(x_18, x_28, x_49);
lean_inc(x_18);
x_51 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_51, 0, x_18);
lean_ctor_set(x_51, 1, x_19);
x_52 = lean_mk_string_unchecked("elabRules", 9, 9);
lean_inc(x_52);
x_53 = l_String_toSubstring_x27(x_52);
x_54 = l_Lean_Name_mkStr1(x_52);
lean_inc(x_26);
lean_inc(x_23);
x_55 = l_Lean_addMacroScope(x_23, x_54, x_26);
x_56 = lean_box(0);
lean_inc(x_18);
x_57 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_57, 0, x_18);
lean_ctor_set(x_57, 1, x_53);
lean_ctor_set(x_57, 2, x_55);
lean_ctor_set(x_57, 3, x_56);
x_58 = lean_mk_syntax_ident(x_4);
lean_inc(x_28);
lean_inc(x_18);
x_59 = l_Lean_Syntax_node2(x_18, x_28, x_57, x_58);
x_60 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_18);
x_61 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_61, 0, x_18);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_mk_string_unchecked("Lean.Elab.Term.TermElab", 23, 23);
x_63 = l_String_toSubstring_x27(x_62);
x_64 = lean_mk_string_unchecked("TermElab", 8, 8);
lean_inc(x_35);
lean_inc(x_24);
lean_inc(x_29);
x_65 = l_Lean_Name_mkStr4(x_29, x_24, x_35, x_64);
lean_inc(x_26);
lean_inc(x_65);
lean_inc(x_23);
x_66 = l_Lean_addMacroScope(x_23, x_65, x_26);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_56);
lean_inc(x_18);
x_70 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_70, 0, x_18);
lean_ctor_set(x_70, 1, x_63);
lean_ctor_set(x_70, 2, x_66);
lean_ctor_set(x_70, 3, x_69);
x_71 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_18);
x_72 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_72, 0, x_18);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_mk_string_unchecked("fun", 3, 3);
lean_inc(x_73);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_29);
x_74 = l_Lean_Name_mkStr4(x_29, x_34, x_35, x_73);
lean_inc(x_18);
x_75 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_75, 0, x_18);
lean_ctor_set(x_75, 1, x_73);
x_76 = lean_mk_string_unchecked("basicFun", 8, 8);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_29);
x_77 = l_Lean_Name_mkStr4(x_29, x_34, x_35, x_76);
x_78 = lean_mk_string_unchecked("stx", 3, 3);
lean_inc(x_78);
x_79 = l_String_toSubstring_x27(x_78);
x_80 = l_Lean_Name_mkStr1(x_78);
lean_inc(x_26);
lean_inc(x_23);
x_81 = l_Lean_addMacroScope(x_23, x_80, x_26);
lean_inc(x_18);
x_82 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_82, 0, x_18);
lean_ctor_set(x_82, 1, x_79);
lean_ctor_set(x_82, 2, x_81);
lean_ctor_set(x_82, 3, x_56);
x_83 = lean_mk_string_unchecked("expectedType\?", 13, 13);
lean_inc(x_83);
x_84 = l_String_toSubstring_x27(x_83);
x_85 = l_Lean_Name_mkStr1(x_83);
lean_inc(x_26);
lean_inc(x_23);
x_86 = l_Lean_addMacroScope(x_23, x_85, x_26);
lean_inc(x_18);
x_87 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_87, 0, x_18);
lean_ctor_set(x_87, 1, x_84);
lean_ctor_set(x_87, 2, x_86);
lean_ctor_set(x_87, 3, x_56);
lean_inc(x_87);
lean_inc(x_82);
lean_inc(x_28);
lean_inc(x_18);
x_88 = l_Lean_Syntax_node2(x_18, x_28, x_82, x_87);
lean_inc(x_30);
lean_inc(x_28);
lean_inc(x_18);
x_89 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_89, 0, x_18);
lean_ctor_set(x_89, 1, x_28);
lean_ctor_set(x_89, 2, x_30);
x_90 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_18);
x_91 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_91, 0, x_18);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_29);
x_93 = l_Lean_Name_mkStr4(x_29, x_34, x_35, x_92);
x_94 = lean_mk_string_unchecked("Lean.Elab.Term.withExpectedType", 31, 31);
x_95 = l_String_toSubstring_x27(x_94);
x_96 = lean_mk_string_unchecked("withExpectedType", 16, 16);
lean_inc(x_35);
lean_inc(x_24);
lean_inc(x_29);
x_97 = l_Lean_Name_mkStr4(x_29, x_24, x_35, x_96);
lean_inc(x_26);
lean_inc(x_97);
lean_inc(x_23);
x_98 = l_Lean_addMacroScope(x_23, x_97, x_26);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_67);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_56);
lean_inc(x_18);
x_101 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_101, 0, x_18);
lean_ctor_set(x_101, 1, x_95);
lean_ctor_set(x_101, 2, x_98);
lean_ctor_set(x_101, 3, x_100);
lean_inc(x_28);
lean_inc(x_18);
x_102 = l_Lean_Syntax_node1(x_18, x_28, x_27);
x_103 = lean_mk_string_unchecked("match", 5, 5);
lean_inc(x_103);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_29);
x_104 = l_Lean_Name_mkStr4(x_29, x_34, x_35, x_103);
lean_inc(x_18);
x_105 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_105, 0, x_18);
lean_ctor_set(x_105, 1, x_103);
x_106 = lean_mk_string_unchecked("matchDiscr", 10, 10);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_29);
x_107 = l_Lean_Name_mkStr4(x_29, x_34, x_35, x_106);
lean_inc(x_89);
lean_inc(x_18);
x_108 = l_Lean_Syntax_node2(x_18, x_107, x_89, x_82);
lean_inc(x_28);
lean_inc(x_18);
x_109 = l_Lean_Syntax_node1(x_18, x_28, x_108);
x_110 = lean_mk_string_unchecked("with", 4, 4);
lean_inc(x_18);
x_111 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_111, 0, x_18);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_mk_string_unchecked("matchAlts", 9, 9);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_29);
x_113 = l_Lean_Name_mkStr4(x_29, x_34, x_35, x_112);
x_114 = lean_mk_string_unchecked("matchAlt", 8, 8);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_29);
x_115 = l_Lean_Name_mkStr4(x_29, x_34, x_35, x_114);
x_116 = l_Array_append(lean_box(0), x_30, x_15);
lean_dec(x_15);
x_117 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_18);
x_118 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_118, 0, x_18);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_mk_string_unchecked("hole", 4, 4);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_29);
x_120 = l_Lean_Name_mkStr4(x_29, x_34, x_35, x_119);
x_121 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_18);
x_122 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_122, 0, x_18);
lean_ctor_set(x_122, 1, x_121);
lean_inc(x_18);
x_123 = l_Lean_Syntax_node1(x_18, x_120, x_122);
lean_inc(x_28);
lean_inc(x_18);
x_124 = l_Lean_Syntax_node1(x_18, x_28, x_123);
lean_inc(x_28);
lean_inc(x_18);
x_125 = l_Lean_Syntax_node1(x_18, x_28, x_124);
x_126 = lean_mk_string_unchecked("noErrorIfUnused", 15, 15);
lean_inc(x_29);
x_127 = l_Lean_Name_mkStr4(x_29, x_34, x_35, x_126);
x_128 = lean_mk_string_unchecked("no_error_if_unused%", 19, 19);
lean_inc(x_18);
x_129 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_129, 0, x_18);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_mk_string_unchecked("throwUnsupportedSyntax", 22, 22);
lean_inc(x_130);
x_131 = l_String_toSubstring_x27(x_130);
lean_inc(x_130);
x_132 = l_Lean_Name_mkStr1(x_130);
x_133 = l_Lean_addMacroScope(x_23, x_132, x_26);
x_134 = l_Lean_Name_mkStr3(x_29, x_24, x_130);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_67);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_56);
lean_inc(x_18);
x_137 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_137, 0, x_18);
lean_ctor_set(x_137, 1, x_131);
lean_ctor_set(x_137, 2, x_133);
lean_ctor_set(x_137, 3, x_136);
lean_inc(x_18);
x_138 = l_Lean_Syntax_node2(x_18, x_127, x_129, x_137);
lean_inc(x_91);
lean_inc(x_18);
x_139 = l_Lean_Syntax_node4(x_18, x_115, x_118, x_125, x_91, x_138);
x_140 = lean_array_push(x_116, x_139);
lean_inc(x_28);
lean_inc(x_18);
x_141 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_141, 0, x_18);
lean_ctor_set(x_141, 1, x_28);
lean_ctor_set(x_141, 2, x_140);
lean_inc(x_18);
x_142 = l_Lean_Syntax_node1(x_18, x_113, x_141);
lean_inc_n(x_89, 2);
lean_inc(x_18);
x_143 = l_Lean_Syntax_node6(x_18, x_104, x_105, x_89, x_89, x_109, x_111, x_142);
lean_inc(x_91);
lean_inc(x_89);
lean_inc(x_77);
lean_inc(x_18);
x_144 = l_Lean_Syntax_node4(x_18, x_77, x_102, x_89, x_91, x_143);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_18);
x_145 = l_Lean_Syntax_node2(x_18, x_74, x_75, x_144);
lean_inc(x_18);
x_146 = l_Lean_Syntax_node2(x_18, x_28, x_87, x_145);
lean_inc(x_18);
x_147 = l_Lean_Syntax_node2(x_18, x_93, x_101, x_146);
lean_inc(x_18);
x_148 = l_Lean_Syntax_node4(x_18, x_77, x_88, x_89, x_91, x_147);
lean_inc(x_18);
x_149 = l_Lean_Syntax_node2(x_18, x_74, x_75, x_148);
x_150 = l_Lean_Syntax_node8(x_18, x_20, x_33, x_50, x_51, x_59, x_61, x_70, x_72, x_149);
if (lean_is_scalar(x_17)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_17;
}
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_21);
return x_151;
}
block_266:
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
lean_inc(x_160);
x_166 = l_Array_append(lean_box(0), x_160, x_165);
lean_dec(x_165);
lean_inc(x_163);
lean_inc(x_162);
x_167 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_167, 0, x_162);
lean_ctor_set(x_167, 1, x_163);
lean_ctor_set(x_167, 2, x_166);
x_168 = lean_mk_string_unchecked("Parser", 6, 6);
x_169 = lean_mk_string_unchecked("Term", 4, 4);
x_170 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_158);
x_171 = l_Lean_Name_mkStr4(x_158, x_168, x_169, x_170);
x_172 = lean_mk_string_unchecked("@[", 2, 2);
lean_inc(x_162);
x_173 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_173, 0, x_162);
lean_ctor_set(x_173, 1, x_172);
x_174 = lean_mk_string_unchecked("attrInstance", 12, 12);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_158);
x_175 = l_Lean_Name_mkStr4(x_158, x_168, x_169, x_174);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_161);
x_177 = lean_mk_string_unchecked(",", 1, 1);
x_178 = l_Lean_Syntax_TSepArray_ofElems(x_176, x_177, x_156);
lean_dec(x_156);
lean_dec(x_176);
lean_inc(x_160);
x_179 = l_Array_append(lean_box(0), x_160, x_178);
lean_dec(x_178);
lean_inc(x_163);
lean_inc(x_162);
x_180 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_180, 0, x_162);
lean_ctor_set(x_180, 1, x_163);
lean_ctor_set(x_180, 2, x_179);
x_181 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_162);
x_182 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_182, 0, x_162);
lean_ctor_set(x_182, 1, x_181);
lean_inc(x_162);
x_183 = l_Lean_Syntax_node3(x_162, x_171, x_173, x_180, x_182);
lean_inc(x_163);
lean_inc(x_162);
x_184 = l_Lean_Syntax_node1(x_162, x_163, x_183);
lean_inc(x_162);
x_185 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_185, 0, x_162);
lean_ctor_set(x_185, 1, x_155);
x_186 = lean_mk_string_unchecked("elabRules", 9, 9);
lean_inc(x_186);
x_187 = l_String_toSubstring_x27(x_186);
x_188 = l_Lean_Name_mkStr1(x_186);
lean_inc(x_157);
lean_inc(x_153);
x_189 = l_Lean_addMacroScope(x_153, x_188, x_157);
x_190 = lean_box(0);
lean_inc(x_162);
x_191 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_191, 0, x_162);
lean_ctor_set(x_191, 1, x_187);
lean_ctor_set(x_191, 2, x_189);
lean_ctor_set(x_191, 3, x_190);
x_192 = lean_mk_syntax_ident(x_4);
lean_inc(x_163);
lean_inc(x_162);
x_193 = l_Lean_Syntax_node2(x_162, x_163, x_191, x_192);
x_194 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_162);
x_195 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_195, 0, x_162);
lean_ctor_set(x_195, 1, x_194);
x_196 = lean_mk_string_unchecked("Lean.Elab.Term.TermElab", 23, 23);
x_197 = l_String_toSubstring_x27(x_196);
x_198 = lean_mk_string_unchecked("TermElab", 8, 8);
lean_inc(x_169);
lean_inc(x_159);
lean_inc(x_158);
x_199 = l_Lean_Name_mkStr4(x_158, x_159, x_169, x_198);
lean_inc(x_157);
lean_inc(x_199);
lean_inc(x_153);
x_200 = l_Lean_addMacroScope(x_153, x_199, x_157);
x_201 = lean_box(0);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_201);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_190);
lean_inc(x_162);
x_204 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_204, 0, x_162);
lean_ctor_set(x_204, 1, x_197);
lean_ctor_set(x_204, 2, x_200);
lean_ctor_set(x_204, 3, x_203);
x_205 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_162);
x_206 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_206, 0, x_162);
lean_ctor_set(x_206, 1, x_205);
x_207 = lean_mk_string_unchecked("fun", 3, 3);
lean_inc(x_207);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_158);
x_208 = l_Lean_Name_mkStr4(x_158, x_168, x_169, x_207);
lean_inc(x_162);
x_209 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_209, 0, x_162);
lean_ctor_set(x_209, 1, x_207);
x_210 = lean_mk_string_unchecked("basicFun", 8, 8);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_158);
x_211 = l_Lean_Name_mkStr4(x_158, x_168, x_169, x_210);
x_212 = lean_mk_string_unchecked("stx", 3, 3);
lean_inc(x_212);
x_213 = l_String_toSubstring_x27(x_212);
x_214 = l_Lean_Name_mkStr1(x_212);
lean_inc(x_157);
lean_inc(x_153);
x_215 = l_Lean_addMacroScope(x_153, x_214, x_157);
lean_inc(x_162);
x_216 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_216, 0, x_162);
lean_ctor_set(x_216, 1, x_213);
lean_ctor_set(x_216, 2, x_215);
lean_ctor_set(x_216, 3, x_190);
x_217 = lean_mk_string_unchecked("hole", 4, 4);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_158);
x_218 = l_Lean_Name_mkStr4(x_158, x_168, x_169, x_217);
x_219 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_162);
x_220 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_220, 0, x_162);
lean_ctor_set(x_220, 1, x_219);
lean_inc(x_162);
x_221 = l_Lean_Syntax_node1(x_162, x_218, x_220);
lean_inc(x_221);
lean_inc(x_216);
lean_inc(x_163);
lean_inc(x_162);
x_222 = l_Lean_Syntax_node2(x_162, x_163, x_216, x_221);
lean_inc(x_160);
lean_inc(x_163);
lean_inc(x_162);
x_223 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_223, 0, x_162);
lean_ctor_set(x_223, 1, x_163);
lean_ctor_set(x_223, 2, x_160);
x_224 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_162);
x_225 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_225, 0, x_162);
lean_ctor_set(x_225, 1, x_224);
x_226 = lean_mk_string_unchecked("match", 5, 5);
lean_inc(x_226);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_158);
x_227 = l_Lean_Name_mkStr4(x_158, x_168, x_169, x_226);
lean_inc(x_162);
x_228 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_228, 0, x_162);
lean_ctor_set(x_228, 1, x_226);
x_229 = lean_mk_string_unchecked("matchDiscr", 10, 10);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_158);
x_230 = l_Lean_Name_mkStr4(x_158, x_168, x_169, x_229);
lean_inc(x_223);
lean_inc(x_162);
x_231 = l_Lean_Syntax_node2(x_162, x_230, x_223, x_216);
lean_inc(x_163);
lean_inc(x_162);
x_232 = l_Lean_Syntax_node1(x_162, x_163, x_231);
x_233 = lean_mk_string_unchecked("with", 4, 4);
lean_inc(x_162);
x_234 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_234, 0, x_162);
lean_ctor_set(x_234, 1, x_233);
x_235 = lean_mk_string_unchecked("matchAlts", 9, 9);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_158);
x_236 = l_Lean_Name_mkStr4(x_158, x_168, x_169, x_235);
x_237 = lean_mk_string_unchecked("matchAlt", 8, 8);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_158);
x_238 = l_Lean_Name_mkStr4(x_158, x_168, x_169, x_237);
x_239 = l_Array_append(lean_box(0), x_160, x_15);
lean_dec(x_15);
x_240 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_162);
x_241 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_241, 0, x_162);
lean_ctor_set(x_241, 1, x_240);
lean_inc(x_163);
lean_inc(x_162);
x_242 = l_Lean_Syntax_node1(x_162, x_163, x_221);
lean_inc(x_163);
lean_inc(x_162);
x_243 = l_Lean_Syntax_node1(x_162, x_163, x_242);
x_244 = lean_mk_string_unchecked("noErrorIfUnused", 15, 15);
lean_inc(x_158);
x_245 = l_Lean_Name_mkStr4(x_158, x_168, x_169, x_244);
x_246 = lean_mk_string_unchecked("no_error_if_unused%", 19, 19);
lean_inc(x_162);
x_247 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_247, 0, x_162);
lean_ctor_set(x_247, 1, x_246);
x_248 = lean_mk_string_unchecked("throwUnsupportedSyntax", 22, 22);
lean_inc(x_248);
x_249 = l_String_toSubstring_x27(x_248);
lean_inc(x_248);
x_250 = l_Lean_Name_mkStr1(x_248);
x_251 = l_Lean_addMacroScope(x_153, x_250, x_157);
x_252 = l_Lean_Name_mkStr3(x_158, x_159, x_248);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_201);
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_190);
lean_inc(x_162);
x_255 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_255, 0, x_162);
lean_ctor_set(x_255, 1, x_249);
lean_ctor_set(x_255, 2, x_251);
lean_ctor_set(x_255, 3, x_254);
lean_inc(x_162);
x_256 = l_Lean_Syntax_node2(x_162, x_245, x_247, x_255);
lean_inc(x_225);
lean_inc(x_162);
x_257 = l_Lean_Syntax_node4(x_162, x_238, x_241, x_243, x_225, x_256);
x_258 = lean_array_push(x_239, x_257);
lean_inc(x_162);
x_259 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_259, 0, x_162);
lean_ctor_set(x_259, 1, x_163);
lean_ctor_set(x_259, 2, x_258);
lean_inc(x_162);
x_260 = l_Lean_Syntax_node1(x_162, x_236, x_259);
lean_inc_n(x_223, 2);
lean_inc(x_162);
x_261 = l_Lean_Syntax_node6(x_162, x_227, x_228, x_223, x_223, x_232, x_234, x_260);
lean_inc(x_162);
x_262 = l_Lean_Syntax_node4(x_162, x_211, x_222, x_223, x_225, x_261);
lean_inc(x_162);
x_263 = l_Lean_Syntax_node2(x_162, x_208, x_209, x_262);
x_264 = l_Lean_Syntax_node8(x_162, x_164, x_167, x_184, x_185, x_193, x_195, x_204, x_206, x_263);
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_154);
return x_265;
}
block_361:
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
lean_inc(x_279);
x_281 = l_Array_append(lean_box(0), x_279, x_280);
lean_dec(x_280);
lean_inc(x_271);
lean_inc(x_274);
x_282 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_282, 0, x_274);
lean_ctor_set(x_282, 1, x_271);
lean_ctor_set(x_282, 2, x_281);
x_283 = lean_mk_string_unchecked("Parser", 6, 6);
x_284 = lean_mk_string_unchecked("Term", 4, 4);
x_285 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_284);
lean_inc(x_283);
lean_inc(x_267);
x_286 = l_Lean_Name_mkStr4(x_267, x_283, x_284, x_285);
x_287 = lean_mk_string_unchecked("@[", 2, 2);
lean_inc(x_274);
x_288 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_288, 0, x_274);
lean_ctor_set(x_288, 1, x_287);
x_289 = lean_mk_string_unchecked("attrInstance", 12, 12);
lean_inc(x_284);
lean_inc(x_283);
lean_inc(x_267);
x_290 = l_Lean_Name_mkStr4(x_267, x_283, x_284, x_289);
x_291 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_268);
x_292 = lean_mk_string_unchecked(",", 1, 1);
x_293 = l_Lean_Syntax_TSepArray_ofElems(x_291, x_292, x_270);
lean_dec(x_270);
lean_dec(x_291);
lean_inc(x_279);
x_294 = l_Array_append(lean_box(0), x_279, x_293);
lean_dec(x_293);
lean_inc(x_271);
lean_inc(x_274);
x_295 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_295, 0, x_274);
lean_ctor_set(x_295, 1, x_271);
lean_ctor_set(x_295, 2, x_294);
x_296 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_274);
x_297 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_297, 0, x_274);
lean_ctor_set(x_297, 1, x_296);
lean_inc(x_274);
x_298 = l_Lean_Syntax_node3(x_274, x_286, x_288, x_295, x_297);
lean_inc(x_271);
lean_inc(x_274);
x_299 = l_Lean_Syntax_node1(x_274, x_271, x_298);
lean_inc(x_274);
x_300 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_300, 0, x_274);
lean_ctor_set(x_300, 1, x_275);
x_301 = lean_mk_string_unchecked("elabRules", 9, 9);
lean_inc(x_301);
x_302 = l_String_toSubstring_x27(x_301);
x_303 = l_Lean_Name_mkStr1(x_301);
lean_inc(x_273);
lean_inc(x_272);
x_304 = l_Lean_addMacroScope(x_272, x_303, x_273);
x_305 = lean_box(0);
lean_inc(x_274);
x_306 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_306, 0, x_274);
lean_ctor_set(x_306, 1, x_302);
lean_ctor_set(x_306, 2, x_304);
lean_ctor_set(x_306, 3, x_305);
x_307 = lean_mk_syntax_ident(x_4);
lean_inc(x_271);
lean_inc(x_274);
x_308 = l_Lean_Syntax_node2(x_274, x_271, x_306, x_307);
x_309 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_274);
x_310 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_310, 0, x_274);
lean_ctor_set(x_310, 1, x_309);
x_311 = lean_mk_string_unchecked("Lean.Elab.Command.CommandElab", 29, 29);
x_312 = l_String_toSubstring_x27(x_311);
x_313 = lean_mk_string_unchecked("CommandElab", 11, 11);
lean_inc(x_277);
lean_inc(x_267);
x_314 = l_Lean_Name_mkStr4(x_267, x_277, x_278, x_313);
lean_inc(x_273);
lean_inc(x_314);
lean_inc(x_272);
x_315 = l_Lean_addMacroScope(x_272, x_314, x_273);
x_316 = lean_box(0);
x_317 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_317, 0, x_314);
lean_ctor_set(x_317, 1, x_316);
x_318 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_318, 1, x_305);
lean_inc(x_274);
x_319 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_319, 0, x_274);
lean_ctor_set(x_319, 1, x_312);
lean_ctor_set(x_319, 2, x_315);
lean_ctor_set(x_319, 3, x_318);
x_320 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_274);
x_321 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_321, 0, x_274);
lean_ctor_set(x_321, 1, x_320);
x_322 = lean_mk_string_unchecked("fun", 3, 3);
lean_inc(x_322);
lean_inc(x_284);
lean_inc(x_283);
lean_inc(x_267);
x_323 = l_Lean_Name_mkStr4(x_267, x_283, x_284, x_322);
lean_inc(x_274);
x_324 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_324, 0, x_274);
lean_ctor_set(x_324, 1, x_322);
x_325 = lean_mk_string_unchecked("matchAlts", 9, 9);
lean_inc(x_284);
lean_inc(x_283);
lean_inc(x_267);
x_326 = l_Lean_Name_mkStr4(x_267, x_283, x_284, x_325);
x_327 = lean_mk_string_unchecked("matchAlt", 8, 8);
lean_inc(x_284);
lean_inc(x_283);
lean_inc(x_267);
x_328 = l_Lean_Name_mkStr4(x_267, x_283, x_284, x_327);
x_329 = l_Array_append(lean_box(0), x_279, x_15);
lean_dec(x_15);
x_330 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_274);
x_331 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_331, 0, x_274);
lean_ctor_set(x_331, 1, x_330);
x_332 = lean_mk_string_unchecked("hole", 4, 4);
lean_inc(x_284);
lean_inc(x_283);
lean_inc(x_267);
x_333 = l_Lean_Name_mkStr4(x_267, x_283, x_284, x_332);
x_334 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_274);
x_335 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_335, 0, x_274);
lean_ctor_set(x_335, 1, x_334);
lean_inc(x_274);
x_336 = l_Lean_Syntax_node1(x_274, x_333, x_335);
lean_inc(x_271);
lean_inc(x_274);
x_337 = l_Lean_Syntax_node1(x_274, x_271, x_336);
lean_inc(x_271);
lean_inc(x_274);
x_338 = l_Lean_Syntax_node1(x_274, x_271, x_337);
x_339 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_274);
x_340 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_340, 0, x_274);
lean_ctor_set(x_340, 1, x_339);
x_341 = lean_mk_string_unchecked("noErrorIfUnused", 15, 15);
lean_inc(x_267);
x_342 = l_Lean_Name_mkStr4(x_267, x_283, x_284, x_341);
x_343 = lean_mk_string_unchecked("no_error_if_unused%", 19, 19);
lean_inc(x_274);
x_344 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_344, 0, x_274);
lean_ctor_set(x_344, 1, x_343);
x_345 = lean_mk_string_unchecked("throwUnsupportedSyntax", 22, 22);
lean_inc(x_345);
x_346 = l_String_toSubstring_x27(x_345);
lean_inc(x_345);
x_347 = l_Lean_Name_mkStr1(x_345);
x_348 = l_Lean_addMacroScope(x_272, x_347, x_273);
x_349 = l_Lean_Name_mkStr3(x_267, x_277, x_345);
x_350 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_350, 0, x_349);
lean_ctor_set(x_350, 1, x_316);
x_351 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_351, 0, x_350);
lean_ctor_set(x_351, 1, x_305);
lean_inc(x_274);
x_352 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_352, 0, x_274);
lean_ctor_set(x_352, 1, x_346);
lean_ctor_set(x_352, 2, x_348);
lean_ctor_set(x_352, 3, x_351);
lean_inc(x_274);
x_353 = l_Lean_Syntax_node2(x_274, x_342, x_344, x_352);
lean_inc(x_274);
x_354 = l_Lean_Syntax_node4(x_274, x_328, x_331, x_338, x_340, x_353);
x_355 = lean_array_push(x_329, x_354);
lean_inc(x_274);
x_356 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_356, 0, x_274);
lean_ctor_set(x_356, 1, x_271);
lean_ctor_set(x_356, 2, x_355);
lean_inc(x_274);
x_357 = l_Lean_Syntax_node1(x_274, x_326, x_356);
lean_inc(x_274);
x_358 = l_Lean_Syntax_node2(x_274, x_323, x_324, x_357);
x_359 = l_Lean_Syntax_node8(x_274, x_276, x_282, x_299, x_300, x_308, x_310, x_319, x_321, x_358);
x_360 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_269);
return x_360;
}
block_455:
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
lean_inc(x_368);
x_375 = l_Array_append(lean_box(0), x_368, x_374);
lean_dec(x_374);
lean_inc(x_372);
lean_inc(x_366);
x_376 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_376, 0, x_366);
lean_ctor_set(x_376, 1, x_372);
lean_ctor_set(x_376, 2, x_375);
x_377 = lean_mk_string_unchecked("Parser", 6, 6);
x_378 = lean_mk_string_unchecked("Term", 4, 4);
x_379 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_378);
lean_inc(x_377);
lean_inc(x_363);
x_380 = l_Lean_Name_mkStr4(x_363, x_377, x_378, x_379);
x_381 = lean_mk_string_unchecked("@[", 2, 2);
lean_inc(x_366);
x_382 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_382, 0, x_366);
lean_ctor_set(x_382, 1, x_381);
x_383 = lean_mk_string_unchecked("attrInstance", 12, 12);
lean_inc(x_378);
lean_inc(x_377);
lean_inc(x_363);
x_384 = l_Lean_Name_mkStr4(x_363, x_377, x_378, x_383);
x_385 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_370);
x_386 = lean_mk_string_unchecked(",", 1, 1);
x_387 = l_Lean_Syntax_TSepArray_ofElems(x_385, x_386, x_369);
lean_dec(x_369);
lean_dec(x_385);
lean_inc(x_368);
x_388 = l_Array_append(lean_box(0), x_368, x_387);
lean_dec(x_387);
lean_inc(x_372);
lean_inc(x_366);
x_389 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_389, 0, x_366);
lean_ctor_set(x_389, 1, x_372);
lean_ctor_set(x_389, 2, x_388);
x_390 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_366);
x_391 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_391, 0, x_366);
lean_ctor_set(x_391, 1, x_390);
lean_inc(x_366);
x_392 = l_Lean_Syntax_node3(x_366, x_380, x_382, x_389, x_391);
lean_inc(x_372);
lean_inc(x_366);
x_393 = l_Lean_Syntax_node1(x_366, x_372, x_392);
lean_inc(x_366);
x_394 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_394, 0, x_366);
lean_ctor_set(x_394, 1, x_365);
x_395 = lean_mk_string_unchecked("elabRules", 9, 9);
lean_inc(x_395);
x_396 = l_String_toSubstring_x27(x_395);
x_397 = l_Lean_Name_mkStr1(x_395);
lean_inc(x_367);
lean_inc(x_371);
x_398 = l_Lean_addMacroScope(x_371, x_397, x_367);
x_399 = lean_box(0);
lean_inc(x_366);
x_400 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_400, 0, x_366);
lean_ctor_set(x_400, 1, x_396);
lean_ctor_set(x_400, 2, x_398);
lean_ctor_set(x_400, 3, x_399);
x_401 = lean_mk_syntax_ident(x_4);
lean_inc(x_372);
lean_inc(x_366);
x_402 = l_Lean_Syntax_node2(x_366, x_372, x_400, x_401);
x_403 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_366);
x_404 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_404, 0, x_366);
lean_ctor_set(x_404, 1, x_403);
x_405 = lean_mk_string_unchecked("Lean.Elab.Tactic.Tactic", 23, 23);
x_406 = l_String_toSubstring_x27(x_405);
x_407 = lean_mk_string_unchecked("Tactic", 6, 6);
lean_inc(x_407);
lean_inc(x_373);
lean_inc(x_363);
x_408 = l_Lean_Name_mkStr4(x_363, x_373, x_407, x_407);
lean_inc(x_367);
lean_inc(x_408);
lean_inc(x_371);
x_409 = l_Lean_addMacroScope(x_371, x_408, x_367);
x_410 = lean_box(0);
x_411 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_411, 0, x_408);
lean_ctor_set(x_411, 1, x_410);
x_412 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_412, 0, x_411);
lean_ctor_set(x_412, 1, x_399);
lean_inc(x_366);
x_413 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_413, 0, x_366);
lean_ctor_set(x_413, 1, x_406);
lean_ctor_set(x_413, 2, x_409);
lean_ctor_set(x_413, 3, x_412);
x_414 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_366);
x_415 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_415, 0, x_366);
lean_ctor_set(x_415, 1, x_414);
x_416 = lean_mk_string_unchecked("fun", 3, 3);
lean_inc(x_416);
lean_inc(x_378);
lean_inc(x_377);
lean_inc(x_363);
x_417 = l_Lean_Name_mkStr4(x_363, x_377, x_378, x_416);
lean_inc(x_366);
x_418 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_418, 0, x_366);
lean_ctor_set(x_418, 1, x_416);
x_419 = lean_mk_string_unchecked("matchAlts", 9, 9);
lean_inc(x_378);
lean_inc(x_377);
lean_inc(x_363);
x_420 = l_Lean_Name_mkStr4(x_363, x_377, x_378, x_419);
x_421 = lean_mk_string_unchecked("matchAlt", 8, 8);
lean_inc(x_378);
lean_inc(x_377);
lean_inc(x_363);
x_422 = l_Lean_Name_mkStr4(x_363, x_377, x_378, x_421);
x_423 = l_Array_append(lean_box(0), x_368, x_15);
lean_dec(x_15);
x_424 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_366);
x_425 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_425, 0, x_366);
lean_ctor_set(x_425, 1, x_424);
x_426 = lean_mk_string_unchecked("hole", 4, 4);
lean_inc(x_378);
lean_inc(x_377);
lean_inc(x_363);
x_427 = l_Lean_Name_mkStr4(x_363, x_377, x_378, x_426);
x_428 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_366);
x_429 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_429, 0, x_366);
lean_ctor_set(x_429, 1, x_428);
lean_inc(x_366);
x_430 = l_Lean_Syntax_node1(x_366, x_427, x_429);
lean_inc(x_372);
lean_inc(x_366);
x_431 = l_Lean_Syntax_node1(x_366, x_372, x_430);
lean_inc(x_372);
lean_inc(x_366);
x_432 = l_Lean_Syntax_node1(x_366, x_372, x_431);
x_433 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_366);
x_434 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_434, 0, x_366);
lean_ctor_set(x_434, 1, x_433);
x_435 = lean_mk_string_unchecked("noErrorIfUnused", 15, 15);
lean_inc(x_363);
x_436 = l_Lean_Name_mkStr4(x_363, x_377, x_378, x_435);
x_437 = lean_mk_string_unchecked("no_error_if_unused%", 19, 19);
lean_inc(x_366);
x_438 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_438, 0, x_366);
lean_ctor_set(x_438, 1, x_437);
x_439 = lean_mk_string_unchecked("throwUnsupportedSyntax", 22, 22);
lean_inc(x_439);
x_440 = l_String_toSubstring_x27(x_439);
lean_inc(x_439);
x_441 = l_Lean_Name_mkStr1(x_439);
x_442 = l_Lean_addMacroScope(x_371, x_441, x_367);
x_443 = l_Lean_Name_mkStr3(x_363, x_373, x_439);
x_444 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_444, 0, x_443);
lean_ctor_set(x_444, 1, x_410);
x_445 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_445, 0, x_444);
lean_ctor_set(x_445, 1, x_399);
lean_inc(x_366);
x_446 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_446, 0, x_366);
lean_ctor_set(x_446, 1, x_440);
lean_ctor_set(x_446, 2, x_442);
lean_ctor_set(x_446, 3, x_445);
lean_inc(x_366);
x_447 = l_Lean_Syntax_node2(x_366, x_436, x_438, x_446);
lean_inc(x_366);
x_448 = l_Lean_Syntax_node4(x_366, x_422, x_425, x_432, x_434, x_447);
x_449 = lean_array_push(x_423, x_448);
lean_inc(x_366);
x_450 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_450, 0, x_366);
lean_ctor_set(x_450, 1, x_372);
lean_ctor_set(x_450, 2, x_449);
lean_inc(x_366);
x_451 = l_Lean_Syntax_node1(x_366, x_420, x_450);
lean_inc(x_366);
x_452 = l_Lean_Syntax_node2(x_366, x_417, x_418, x_451);
x_453 = l_Lean_Syntax_node8(x_366, x_362, x_376, x_393, x_394, x_402, x_404, x_413, x_415, x_452);
x_454 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_454, 0, x_453);
lean_ctor_set(x_454, 1, x_364);
return x_454;
}
block_486:
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
lean_inc(x_4);
x_461 = l_Lean_Elab_Command_elabElabRulesAux___lam__0(x_4, x_3, x_2, x_459, x_456, x_457, x_458);
x_462 = lean_ctor_get(x_461, 0);
lean_inc(x_462);
x_463 = lean_ctor_get(x_461, 1);
lean_inc(x_463);
lean_dec(x_461);
x_464 = l_Lean_Elab_Command_getRef(x_456, x_457, x_463);
x_465 = lean_ctor_get(x_464, 0);
lean_inc(x_465);
x_466 = lean_ctor_get(x_464, 1);
lean_inc(x_466);
lean_dec(x_464);
x_467 = l_Lean_Elab_Command_getCurrMacroScope(x_456, x_457, x_466);
lean_dec(x_456);
x_468 = lean_ctor_get(x_467, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_467, 1);
lean_inc(x_469);
lean_dec(x_467);
x_470 = l_Lean_Elab_Command_getMainModule___redArg(x_457, x_469);
x_471 = lean_ctor_get(x_470, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_470, 1);
lean_inc(x_472);
lean_dec(x_470);
x_473 = l_Lean_SourceInfo_fromRef(x_465, x_460);
lean_dec(x_465);
x_474 = lean_box(0);
x_475 = lean_mk_string_unchecked("Lean", 4, 4);
x_476 = lean_mk_string_unchecked("Elab", 4, 4);
x_477 = lean_mk_string_unchecked("Command", 7, 7);
x_478 = lean_mk_string_unchecked("aux_def", 7, 7);
lean_inc(x_478);
lean_inc(x_476);
lean_inc(x_475);
x_479 = l_Lean_Name_mkStr4(x_475, x_476, x_477, x_478);
x_480 = lean_mk_string_unchecked("null", 4, 4);
x_481 = l_Lean_Name_mkStr1(x_480);
x_482 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_483; 
x_483 = l_Array_empty(lean_box(0));
x_362 = x_479;
x_363 = x_475;
x_364 = x_472;
x_365 = x_478;
x_366 = x_473;
x_367 = x_468;
x_368 = x_482;
x_369 = x_462;
x_370 = x_474;
x_371 = x_471;
x_372 = x_481;
x_373 = x_476;
x_374 = x_483;
goto block_455;
}
else
{
lean_object* x_484; lean_object* x_485; 
x_484 = lean_ctor_get(x_1, 0);
lean_inc(x_484);
lean_dec(x_1);
x_485 = l_Array_mkArray1___redArg(x_484);
x_362 = x_479;
x_363 = x_475;
x_364 = x_472;
x_365 = x_478;
x_366 = x_473;
x_367 = x_468;
x_368 = x_482;
x_369 = x_462;
x_370 = x_474;
x_371 = x_471;
x_372 = x_481;
x_373 = x_476;
x_374 = x_485;
goto block_455;
}
}
block_608:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_491; lean_object* x_492; uint8_t x_493; 
lean_dec(x_17);
x_491 = lean_mk_string_unchecked("term", 4, 4);
x_492 = l_Lean_Name_mkStr1(x_491);
x_493 = lean_name_eq(x_487, x_492);
lean_dec(x_492);
if (x_493 == 0)
{
lean_object* x_494; lean_object* x_495; uint8_t x_496; 
x_494 = lean_mk_string_unchecked("command", 7, 7);
x_495 = l_Lean_Name_mkStr1(x_494);
x_496 = lean_name_eq(x_487, x_495);
lean_dec(x_495);
if (x_496 == 0)
{
lean_object* x_497; lean_object* x_498; uint8_t x_499; 
x_497 = lean_mk_string_unchecked("tactic", 6, 6);
x_498 = l_Lean_Name_mkStr1(x_497);
x_499 = lean_name_eq(x_487, x_498);
if (x_499 == 0)
{
lean_object* x_500; lean_object* x_501; uint8_t x_502; 
x_500 = lean_mk_string_unchecked("conv", 4, 4);
x_501 = l_Lean_Name_mkStr1(x_500);
x_502 = lean_name_eq(x_487, x_501);
lean_dec(x_501);
if (x_502 == 0)
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; 
lean_dec(x_498);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_503 = lean_mk_string_unchecked("unsupported syntax category '", 29, 29);
x_504 = l_Lean_stringToMessageData(x_503);
lean_dec(x_503);
x_505 = l_Lean_MessageData_ofName(x_487);
x_506 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_506, 0, x_504);
lean_ctor_set(x_506, 1, x_505);
x_507 = lean_mk_string_unchecked("'", 1, 1);
x_508 = l_Lean_stringToMessageData(x_507);
lean_dec(x_507);
x_509 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_509, 0, x_506);
lean_ctor_set(x_509, 1, x_508);
x_510 = l_Lean_throwError___at_____private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_spec__0___redArg(x_509, x_488, x_489, x_490);
return x_510;
}
else
{
lean_dec(x_487);
x_456 = x_488;
x_457 = x_489;
x_458 = x_490;
x_459 = x_498;
x_460 = x_496;
goto block_486;
}
}
else
{
lean_dec(x_487);
x_456 = x_488;
x_457 = x_489;
x_458 = x_490;
x_459 = x_498;
x_460 = x_496;
goto block_486;
}
}
else
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; 
lean_dec(x_487);
x_511 = lean_mk_string_unchecked("command_elab", 12, 12);
x_512 = l_Lean_Name_mkStr1(x_511);
lean_inc(x_4);
x_513 = l_Lean_Elab_Command_elabElabRulesAux___lam__0(x_4, x_3, x_2, x_512, x_488, x_489, x_490);
x_514 = lean_ctor_get(x_513, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_513, 1);
lean_inc(x_515);
lean_dec(x_513);
x_516 = l_Lean_Elab_Command_getRef(x_488, x_489, x_515);
x_517 = lean_ctor_get(x_516, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_516, 1);
lean_inc(x_518);
lean_dec(x_516);
x_519 = l_Lean_Elab_Command_getCurrMacroScope(x_488, x_489, x_518);
lean_dec(x_488);
x_520 = lean_ctor_get(x_519, 0);
lean_inc(x_520);
x_521 = lean_ctor_get(x_519, 1);
lean_inc(x_521);
lean_dec(x_519);
x_522 = l_Lean_Elab_Command_getMainModule___redArg(x_489, x_521);
x_523 = lean_ctor_get(x_522, 0);
lean_inc(x_523);
x_524 = lean_ctor_get(x_522, 1);
lean_inc(x_524);
lean_dec(x_522);
x_525 = l_Lean_SourceInfo_fromRef(x_517, x_493);
lean_dec(x_517);
x_526 = lean_box(0);
x_527 = lean_mk_string_unchecked("Lean", 4, 4);
x_528 = lean_mk_string_unchecked("Elab", 4, 4);
x_529 = lean_mk_string_unchecked("Command", 7, 7);
x_530 = lean_mk_string_unchecked("aux_def", 7, 7);
lean_inc(x_530);
lean_inc(x_529);
lean_inc(x_528);
lean_inc(x_527);
x_531 = l_Lean_Name_mkStr4(x_527, x_528, x_529, x_530);
x_532 = lean_mk_string_unchecked("null", 4, 4);
x_533 = l_Lean_Name_mkStr1(x_532);
x_534 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_535; 
x_535 = l_Array_empty(lean_box(0));
x_267 = x_527;
x_268 = x_526;
x_269 = x_524;
x_270 = x_514;
x_271 = x_533;
x_272 = x_523;
x_273 = x_520;
x_274 = x_525;
x_275 = x_530;
x_276 = x_531;
x_277 = x_528;
x_278 = x_529;
x_279 = x_534;
x_280 = x_535;
goto block_361;
}
else
{
lean_object* x_536; lean_object* x_537; 
x_536 = lean_ctor_get(x_1, 0);
lean_inc(x_536);
lean_dec(x_1);
x_537 = l_Array_mkArray1___redArg(x_536);
x_267 = x_527;
x_268 = x_526;
x_269 = x_524;
x_270 = x_514;
x_271 = x_533;
x_272 = x_523;
x_273 = x_520;
x_274 = x_525;
x_275 = x_530;
x_276 = x_531;
x_277 = x_528;
x_278 = x_529;
x_279 = x_534;
x_280 = x_537;
goto block_361;
}
}
}
else
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; uint8_t x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; 
lean_dec(x_487);
x_538 = lean_mk_string_unchecked("term_elab", 9, 9);
x_539 = l_Lean_Name_mkStr1(x_538);
lean_inc(x_4);
x_540 = l_Lean_Elab_Command_elabElabRulesAux___lam__0(x_4, x_3, x_2, x_539, x_488, x_489, x_490);
x_541 = lean_ctor_get(x_540, 0);
lean_inc(x_541);
x_542 = lean_ctor_get(x_540, 1);
lean_inc(x_542);
lean_dec(x_540);
x_543 = l_Lean_Elab_Command_getRef(x_488, x_489, x_542);
x_544 = lean_ctor_get(x_543, 0);
lean_inc(x_544);
x_545 = lean_ctor_get(x_543, 1);
lean_inc(x_545);
lean_dec(x_543);
x_546 = l_Lean_Elab_Command_getCurrMacroScope(x_488, x_489, x_545);
lean_dec(x_488);
x_547 = lean_ctor_get(x_546, 0);
lean_inc(x_547);
x_548 = lean_ctor_get(x_546, 1);
lean_inc(x_548);
lean_dec(x_546);
x_549 = l_Lean_Elab_Command_getMainModule___redArg(x_489, x_548);
x_550 = lean_ctor_get(x_549, 0);
lean_inc(x_550);
x_551 = lean_ctor_get(x_549, 1);
lean_inc(x_551);
lean_dec(x_549);
x_552 = lean_box(0);
x_553 = lean_unbox(x_552);
x_554 = l_Lean_SourceInfo_fromRef(x_544, x_553);
lean_dec(x_544);
x_555 = lean_box(0);
x_556 = lean_mk_string_unchecked("Lean", 4, 4);
x_557 = lean_mk_string_unchecked("Elab", 4, 4);
x_558 = lean_mk_string_unchecked("Command", 7, 7);
x_559 = lean_mk_string_unchecked("aux_def", 7, 7);
lean_inc(x_559);
lean_inc(x_557);
lean_inc(x_556);
x_560 = l_Lean_Name_mkStr4(x_556, x_557, x_558, x_559);
x_561 = lean_mk_string_unchecked("null", 4, 4);
x_562 = l_Lean_Name_mkStr1(x_561);
x_563 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_564; 
x_564 = l_Array_empty(lean_box(0));
x_153 = x_550;
x_154 = x_551;
x_155 = x_559;
x_156 = x_541;
x_157 = x_547;
x_158 = x_556;
x_159 = x_557;
x_160 = x_563;
x_161 = x_555;
x_162 = x_554;
x_163 = x_562;
x_164 = x_560;
x_165 = x_564;
goto block_266;
}
else
{
lean_object* x_565; lean_object* x_566; 
x_565 = lean_ctor_get(x_1, 0);
lean_inc(x_565);
lean_dec(x_1);
x_566 = l_Array_mkArray1___redArg(x_565);
x_153 = x_550;
x_154 = x_551;
x_155 = x_559;
x_156 = x_541;
x_157 = x_547;
x_158 = x_556;
x_159 = x_557;
x_160 = x_563;
x_161 = x_555;
x_162 = x_554;
x_163 = x_562;
x_164 = x_560;
x_165 = x_566;
goto block_266;
}
}
}
else
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; uint8_t x_570; 
x_567 = lean_ctor_get(x_6, 0);
lean_inc(x_567);
lean_dec(x_6);
x_568 = lean_mk_string_unchecked("term", 4, 4);
x_569 = l_Lean_Name_mkStr1(x_568);
x_570 = lean_name_eq(x_487, x_569);
lean_dec(x_569);
if (x_570 == 0)
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_571 = lean_mk_string_unchecked("syntax category '", 17, 17);
x_572 = l_Lean_stringToMessageData(x_571);
lean_dec(x_571);
x_573 = l_Lean_MessageData_ofName(x_487);
x_574 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_574, 0, x_572);
lean_ctor_set(x_574, 1, x_573);
x_575 = lean_mk_string_unchecked("' does not support expected type specification", 46, 46);
x_576 = l_Lean_stringToMessageData(x_575);
lean_dec(x_575);
x_577 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_577, 0, x_574);
lean_ctor_set(x_577, 1, x_576);
x_578 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_567, x_577, x_488, x_489, x_490);
lean_dec(x_488);
lean_dec(x_567);
return x_578;
}
else
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; uint8_t x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; 
lean_dec(x_487);
x_579 = lean_mk_string_unchecked("term_elab", 9, 9);
x_580 = l_Lean_Name_mkStr1(x_579);
lean_inc(x_4);
x_581 = l_Lean_Elab_Command_elabElabRulesAux___lam__0(x_4, x_3, x_2, x_580, x_488, x_489, x_490);
x_582 = lean_ctor_get(x_581, 0);
lean_inc(x_582);
x_583 = lean_ctor_get(x_581, 1);
lean_inc(x_583);
lean_dec(x_581);
x_584 = l_Lean_Elab_Command_getRef(x_488, x_489, x_583);
x_585 = lean_ctor_get(x_584, 0);
lean_inc(x_585);
x_586 = lean_ctor_get(x_584, 1);
lean_inc(x_586);
lean_dec(x_584);
x_587 = l_Lean_Elab_Command_getCurrMacroScope(x_488, x_489, x_586);
lean_dec(x_488);
x_588 = lean_ctor_get(x_587, 0);
lean_inc(x_588);
x_589 = lean_ctor_get(x_587, 1);
lean_inc(x_589);
lean_dec(x_587);
x_590 = l_Lean_Elab_Command_getMainModule___redArg(x_489, x_589);
x_591 = lean_ctor_get(x_590, 0);
lean_inc(x_591);
x_592 = lean_ctor_get(x_590, 1);
lean_inc(x_592);
lean_dec(x_590);
x_593 = lean_box(0);
x_594 = lean_unbox(x_593);
x_595 = l_Lean_SourceInfo_fromRef(x_585, x_594);
lean_dec(x_585);
x_596 = lean_box(0);
x_597 = lean_mk_string_unchecked("Lean", 4, 4);
x_598 = lean_mk_string_unchecked("Elab", 4, 4);
x_599 = lean_mk_string_unchecked("Command", 7, 7);
x_600 = lean_mk_string_unchecked("aux_def", 7, 7);
lean_inc(x_600);
lean_inc(x_598);
lean_inc(x_597);
x_601 = l_Lean_Name_mkStr4(x_597, x_598, x_599, x_600);
x_602 = lean_mk_string_unchecked("null", 4, 4);
x_603 = l_Lean_Name_mkStr1(x_602);
x_604 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_605; 
x_605 = l_Array_empty(lean_box(0));
x_18 = x_595;
x_19 = x_600;
x_20 = x_601;
x_21 = x_592;
x_22 = x_582;
x_23 = x_591;
x_24 = x_598;
x_25 = x_596;
x_26 = x_588;
x_27 = x_567;
x_28 = x_603;
x_29 = x_597;
x_30 = x_604;
x_31 = x_605;
goto block_152;
}
else
{
lean_object* x_606; lean_object* x_607; 
x_606 = lean_ctor_get(x_1, 0);
lean_inc(x_606);
lean_dec(x_1);
x_607 = l_Array_mkArray1___redArg(x_606);
x_18 = x_595;
x_19 = x_600;
x_20 = x_601;
x_21 = x_592;
x_22 = x_582;
x_23 = x_591;
x_24 = x_598;
x_25 = x_596;
x_26 = x_588;
x_27 = x_567;
x_28 = x_603;
x_29 = x_597;
x_30 = x_604;
x_31 = x_607;
goto block_152;
}
}
}
}
}
else
{
uint8_t x_620; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_620 = !lean_is_exclusive(x_14);
if (x_620 == 0)
{
return x_14;
}
else
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; 
x_621 = lean_ctor_get(x_14, 0);
x_622 = lean_ctor_get(x_14, 1);
lean_inc(x_622);
lean_inc(x_621);
lean_dec(x_14);
x_623 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_623, 0, x_621);
lean_ctor_set(x_623, 1, x_622);
return x_623;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___Lean_Elab_Command_elabElabRulesAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_mkIdentFromRef___at___Lean_Elab_Command_elabElabRulesAux_spec__0(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabElabRulesAux_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_elabElabRulesAux_spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Elab_Command_elabElabRulesAux_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Elab_Command_elabElabRulesAux_spec__2_spec__2(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabElabRulesAux_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabElabRulesAux_spec__2(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Command_elabElabRulesAux___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Command_elabElabRulesAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_72; lean_object* x_73; lean_object* x_90; 
x_17 = l_Lean_Elab_Command_getRef(x_14, x_15, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_20 = x_17;
} else {
 lean_dec_ref(x_17);
 x_20 = lean_box(0);
}
x_21 = l_Lean_Elab_Command_getCurrMacroScope(x_14, x_15, x_19);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_23 = x_21;
} else {
 lean_dec_ref(x_21);
 x_23 = lean_box(0);
}
x_24 = l_Lean_Elab_Command_getMainModule___redArg(x_15, x_22);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_26 = x_24;
} else {
 lean_dec_ref(x_24);
 x_26 = lean_box(0);
}
x_27 = lean_box(0);
x_28 = lean_unbox(x_27);
x_29 = l_Lean_SourceInfo_fromRef(x_18, x_28);
lean_dec(x_18);
x_30 = lean_mk_string_unchecked("null", 4, 4);
x_31 = l_Lean_Name_mkStr1(x_30);
x_32 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_106; 
x_106 = l_Array_empty(lean_box(0));
x_90 = x_106;
goto block_105;
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_11, 0);
lean_inc(x_107);
lean_dec(x_11);
x_108 = l_Array_mkArray1___redArg(x_107);
x_90 = x_108;
goto block_105;
}
block_46:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_inc(x_32);
x_39 = l_Array_append(lean_box(0), x_32, x_38);
lean_dec(x_38);
lean_inc(x_31);
lean_inc(x_29);
x_40 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_40, 0, x_29);
lean_ctor_set(x_40, 1, x_31);
lean_ctor_set(x_40, 2, x_39);
x_41 = l_Array_append(lean_box(0), x_32, x_13);
lean_inc(x_29);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_29);
lean_ctor_set(x_42, 1, x_31);
lean_ctor_set(x_42, 2, x_41);
lean_inc(x_29);
x_43 = l_Lean_Syntax_node1(x_29, x_1, x_42);
x_44 = l_Lean_Syntax_node8(x_29, x_2, x_37, x_35, x_3, x_33, x_34, x_36, x_40, x_43);
if (lean_is_scalar(x_26)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_26;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_25);
return x_45;
}
block_59:
{
lean_object* x_52; lean_object* x_53; 
lean_inc(x_32);
x_52 = l_Array_append(lean_box(0), x_32, x_51);
lean_dec(x_51);
lean_inc(x_31);
lean_inc(x_29);
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_29);
lean_ctor_set(x_53, 1, x_31);
lean_ctor_set(x_53, 2, x_52);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_54; 
lean_dec(x_23);
x_54 = l_Array_empty(lean_box(0));
x_33 = x_47;
x_34 = x_48;
x_35 = x_49;
x_36 = x_53;
x_37 = x_50;
x_38 = x_54;
goto block_46;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_4, 0);
lean_inc(x_55);
lean_dec(x_4);
x_56 = lean_mk_string_unchecked("<=", 2, 2);
lean_inc(x_29);
if (lean_is_scalar(x_23)) {
 x_57 = lean_alloc_ctor(2, 2, 0);
} else {
 x_57 = x_23;
 lean_ctor_set_tag(x_57, 2);
}
lean_ctor_set(x_57, 0, x_29);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Array_mkArray2(lean_box(0), x_57, x_55);
x_33 = x_47;
x_34 = x_48;
x_35 = x_49;
x_36 = x_53;
x_37 = x_50;
x_38 = x_58;
goto block_46;
}
}
block_71:
{
lean_object* x_64; lean_object* x_65; 
lean_inc(x_32);
x_64 = l_Array_append(lean_box(0), x_32, x_63);
lean_dec(x_63);
lean_inc(x_31);
lean_inc(x_29);
x_65 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_65, 0, x_29);
lean_ctor_set(x_65, 1, x_31);
lean_ctor_set(x_65, 2, x_64);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_66; 
lean_dec(x_20);
x_66 = l_Array_empty(lean_box(0));
x_47 = x_60;
x_48 = x_65;
x_49 = x_61;
x_50 = x_62;
x_51 = x_66;
goto block_59;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_5, 0);
lean_inc(x_67);
lean_dec(x_5);
x_68 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_29);
if (lean_is_scalar(x_20)) {
 x_69 = lean_alloc_ctor(2, 2, 0);
} else {
 x_69 = x_20;
 lean_ctor_set_tag(x_69, 2);
}
lean_ctor_set(x_69, 0, x_29);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Array_mkArray2(lean_box(0), x_69, x_67);
x_47 = x_60;
x_48 = x_65;
x_49 = x_61;
x_50 = x_62;
x_51 = x_70;
goto block_59;
}
}
block_89:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_inc(x_32);
x_74 = l_Array_append(lean_box(0), x_32, x_73);
lean_dec(x_73);
lean_inc(x_31);
lean_inc(x_29);
x_75 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_75, 0, x_29);
lean_ctor_set(x_75, 1, x_31);
lean_ctor_set(x_75, 2, x_74);
lean_inc(x_29);
x_76 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_76, 0, x_29);
lean_ctor_set(x_76, 1, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_77; 
x_77 = l_Array_empty(lean_box(0));
x_60 = x_76;
x_61 = x_75;
x_62 = x_72;
x_63 = x_77;
goto block_71;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_78 = lean_ctor_get(x_12, 0);
lean_inc(x_78);
lean_dec(x_12);
x_79 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_29);
x_80 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_80, 0, x_29);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_mk_string_unchecked("kind", 4, 4);
lean_inc(x_29);
x_82 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_82, 0, x_29);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_29);
x_84 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_84, 0, x_29);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_mk_syntax_ident(x_78);
x_86 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_29);
x_87 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_87, 0, x_29);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Array_mkArray5(lean_box(0), x_80, x_82, x_84, x_85, x_87);
x_60 = x_76;
x_61 = x_75;
x_62 = x_72;
x_63 = x_88;
goto block_71;
}
}
block_105:
{
lean_object* x_91; lean_object* x_92; 
lean_inc(x_32);
x_91 = l_Array_append(lean_box(0), x_32, x_90);
lean_dec(x_90);
lean_inc(x_31);
lean_inc(x_29);
x_92 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_92, 0, x_29);
lean_ctor_set(x_92, 1, x_31);
lean_ctor_set(x_92, 2, x_91);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_93; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_93 = l_Array_empty(lean_box(0));
x_72 = x_92;
x_73 = x_93;
goto block_89;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_94 = lean_ctor_get(x_7, 0);
x_95 = lean_mk_string_unchecked("attributes", 10, 10);
x_96 = l_Lean_Name_mkStr4(x_8, x_9, x_10, x_95);
x_97 = lean_mk_string_unchecked("@[", 2, 2);
lean_inc(x_29);
x_98 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_98, 0, x_29);
lean_ctor_set(x_98, 1, x_97);
lean_inc(x_32);
x_99 = l_Array_append(lean_box(0), x_32, x_94);
lean_inc(x_31);
lean_inc(x_29);
x_100 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_100, 0, x_29);
lean_ctor_set(x_100, 1, x_31);
lean_ctor_set(x_100, 2, x_99);
x_101 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_29);
x_102 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_102, 0, x_29);
lean_ctor_set(x_102, 1, x_101);
lean_inc(x_29);
x_103 = l_Lean_Syntax_node3(x_29, x_96, x_98, x_100, x_102);
x_104 = l_Array_mkArray1___redArg(x_103);
x_72 = x_92;
x_73 = x_104;
goto block_89;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("Parser", 6, 6);
x_7 = lean_mk_string_unchecked("Command", 7, 7);
x_8 = lean_mk_string_unchecked("elab_rules", 10, 10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_9 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_8);
lean_inc(x_1);
x_10 = l_Lean_Syntax_isOfKind(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_166; uint8_t x_167; 
x_12 = lean_unsigned_to_nat(0u);
x_166 = l_Lean_Syntax_getArg(x_1, x_12);
x_167 = l_Lean_Syntax_isNone(x_166);
if (x_167 == 0)
{
lean_object* x_168; uint8_t x_169; 
x_168 = lean_unsigned_to_nat(1u);
lean_inc(x_166);
x_169 = l_Lean_Syntax_matchesNull(x_166, x_168);
if (x_169 == 0)
{
lean_object* x_170; 
lean_dec(x_166);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_170 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_170;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_171 = l_Lean_Syntax_getArg(x_166, x_12);
lean_dec(x_166);
x_172 = lean_mk_string_unchecked("docComment", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
x_173 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_172);
lean_inc(x_171);
x_174 = l_Lean_Syntax_isOfKind(x_171, x_173);
lean_dec(x_173);
if (x_174 == 0)
{
lean_object* x_175; 
lean_dec(x_171);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_175 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_175;
}
else
{
lean_object* x_176; 
x_176 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_176, 0, x_171);
x_146 = x_176;
x_147 = x_2;
x_148 = x_3;
x_149 = x_4;
goto block_165;
}
}
}
else
{
lean_object* x_177; 
lean_dec(x_166);
lean_dec(x_7);
x_177 = lean_box(0);
x_146 = x_177;
x_147 = x_2;
x_148 = x_3;
x_149 = x_4;
goto block_165;
}
block_40:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_unsigned_to_nat(7u);
x_22 = l_Lean_Syntax_getArg(x_1, x_21);
lean_dec(x_1);
x_23 = lean_mk_string_unchecked("Term", 4, 4);
x_24 = lean_mk_string_unchecked("matchAlts", 9, 9);
lean_inc(x_23);
lean_inc(x_6);
lean_inc(x_5);
x_25 = l_Lean_Name_mkStr4(x_5, x_6, x_23, x_24);
lean_inc(x_22);
x_26 = l_Lean_Syntax_isOfKind(x_22, x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_27 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_15, x_19, x_13);
lean_dec(x_19);
lean_dec(x_15);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_inc(x_8);
x_28 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElabRules___lam__0___boxed), 16, 11);
lean_closure_set(x_28, 0, x_25);
lean_closure_set(x_28, 1, x_9);
lean_closure_set(x_28, 2, x_14);
lean_closure_set(x_28, 3, x_20);
lean_closure_set(x_28, 4, x_17);
lean_closure_set(x_28, 5, x_8);
lean_closure_set(x_28, 6, x_16);
lean_closure_set(x_28, 7, x_5);
lean_closure_set(x_28, 8, x_6);
lean_closure_set(x_28, 9, x_23);
lean_closure_set(x_28, 10, x_18);
x_29 = l_Lean_Syntax_getArg(x_22, x_12);
lean_dec(x_22);
x_30 = l_Lean_Syntax_getArgs(x_29);
lean_dec(x_29);
x_31 = l_Lean_Elab_Command_expandNoKindMacroRulesAux(x_30, x_8, x_28, x_15, x_19, x_13);
lean_dec(x_8);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
return x_31;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
block_58:
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_unsigned_to_nat(6u);
x_51 = l_Lean_Syntax_getArg(x_1, x_50);
x_52 = l_Lean_Syntax_isNone(x_51);
if (x_52 == 0)
{
uint8_t x_53; 
lean_inc(x_51);
x_53 = l_Lean_Syntax_matchesNull(x_51, x_44);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_51);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_54 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_47, x_48, x_49);
lean_dec(x_48);
lean_dec(x_47);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = l_Lean_Syntax_getArg(x_51, x_45);
lean_dec(x_51);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_13 = x_49;
x_14 = x_41;
x_15 = x_47;
x_16 = x_42;
x_17 = x_46;
x_18 = x_43;
x_19 = x_48;
x_20 = x_56;
goto block_40;
}
}
else
{
lean_object* x_57; 
lean_dec(x_51);
x_57 = lean_box(0);
x_13 = x_49;
x_14 = x_41;
x_15 = x_47;
x_16 = x_42;
x_17 = x_46;
x_18 = x_43;
x_19 = x_48;
x_20 = x_57;
goto block_40;
}
}
block_89:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_70 = lean_unsigned_to_nat(7u);
x_71 = l_Lean_Syntax_getArg(x_1, x_70);
x_72 = lean_mk_string_unchecked("matchAlts", 9, 9);
x_73 = l_Lean_Name_mkStr4(x_5, x_6, x_65, x_72);
lean_inc(x_71);
x_74 = l_Lean_Syntax_isOfKind(x_71, x_73);
lean_dec(x_73);
if (x_74 == 0)
{
lean_object* x_75; 
lean_dec(x_71);
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_1);
x_75 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_67, x_68, x_69);
lean_dec(x_68);
lean_dec(x_67);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = l_Lean_Syntax_getArg(x_59, x_63);
lean_dec(x_59);
x_77 = l_Lean_Syntax_getId(x_76);
lean_dec(x_76);
lean_inc(x_67);
x_78 = l_Lean_Elab_Command_resolveSyntaxKind(x_77, x_67, x_68, x_69);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l_Lean_Syntax_getArg(x_71, x_12);
lean_dec(x_71);
x_82 = l_Lean_Syntax_getArgs(x_81);
lean_dec(x_81);
x_83 = l_Lean_Syntax_getArg(x_1, x_62);
lean_dec(x_1);
x_84 = l_Lean_Elab_Command_elabElabRulesAux(x_61, x_64, x_83, x_79, x_60, x_66, x_82, x_67, x_68, x_80);
lean_dec(x_68);
lean_dec(x_60);
lean_dec(x_64);
return x_84;
}
else
{
uint8_t x_85; 
lean_dec(x_71);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_78);
if (x_85 == 0)
{
return x_78;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_78, 0);
x_87 = lean_ctor_get(x_78, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_78);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
block_109:
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = lean_unsigned_to_nat(6u);
x_102 = l_Lean_Syntax_getArg(x_1, x_101);
x_103 = l_Lean_Syntax_isNone(x_102);
if (x_103 == 0)
{
uint8_t x_104; 
lean_inc(x_102);
x_104 = l_Lean_Syntax_matchesNull(x_102, x_91);
if (x_104 == 0)
{
lean_object* x_105; 
lean_dec(x_102);
lean_dec(x_97);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_92);
lean_dec(x_90);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_105 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_98, x_99, x_100);
lean_dec(x_99);
lean_dec(x_98);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = l_Lean_Syntax_getArg(x_102, x_96);
lean_dec(x_102);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_59 = x_90;
x_60 = x_97;
x_61 = x_92;
x_62 = x_91;
x_63 = x_93;
x_64 = x_95;
x_65 = x_94;
x_66 = x_107;
x_67 = x_98;
x_68 = x_99;
x_69 = x_100;
goto block_89;
}
}
else
{
lean_object* x_108; 
lean_dec(x_102);
x_108 = lean_box(0);
x_59 = x_90;
x_60 = x_97;
x_61 = x_92;
x_62 = x_91;
x_63 = x_93;
x_64 = x_95;
x_65 = x_94;
x_66 = x_108;
x_67 = x_98;
x_68 = x_99;
x_69 = x_100;
goto block_89;
}
}
block_145:
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_116 = lean_unsigned_to_nat(2u);
x_117 = l_Lean_Syntax_getArg(x_1, x_116);
x_118 = lean_mk_string_unchecked("Term", 4, 4);
x_119 = lean_mk_string_unchecked("attrKind", 8, 8);
lean_inc(x_118);
lean_inc(x_6);
lean_inc(x_5);
x_120 = l_Lean_Name_mkStr4(x_5, x_6, x_118, x_119);
lean_inc(x_117);
x_121 = l_Lean_Syntax_isOfKind(x_117, x_120);
lean_dec(x_120);
if (x_121 == 0)
{
lean_object* x_122; 
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_115);
lean_dec(x_112);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_122 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_110, x_111, x_113);
lean_dec(x_111);
lean_dec(x_110);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_123 = lean_unsigned_to_nat(4u);
x_124 = l_Lean_Syntax_getArg(x_1, x_123);
lean_inc(x_124);
x_125 = l_Lean_Syntax_matchesNull(x_124, x_12);
if (x_125 == 0)
{
lean_object* x_126; uint8_t x_127; 
lean_dec(x_117);
lean_dec(x_9);
lean_dec(x_8);
x_126 = lean_unsigned_to_nat(5u);
lean_inc(x_124);
x_127 = l_Lean_Syntax_matchesNull(x_124, x_126);
if (x_127 == 0)
{
lean_object* x_128; 
lean_dec(x_124);
lean_dec(x_118);
lean_dec(x_115);
lean_dec(x_112);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_128 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_110, x_111, x_113);
lean_dec(x_111);
lean_dec(x_110);
return x_128;
}
else
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_129 = lean_unsigned_to_nat(3u);
x_130 = l_Lean_Syntax_getArg(x_1, x_126);
x_131 = l_Lean_Syntax_isNone(x_130);
if (x_131 == 0)
{
uint8_t x_132; 
lean_inc(x_130);
x_132 = l_Lean_Syntax_matchesNull(x_130, x_116);
if (x_132 == 0)
{
lean_object* x_133; 
lean_dec(x_130);
lean_dec(x_124);
lean_dec(x_118);
lean_dec(x_115);
lean_dec(x_112);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_133 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_110, x_111, x_113);
lean_dec(x_111);
lean_dec(x_110);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; 
x_134 = l_Lean_Syntax_getArg(x_130, x_114);
lean_dec(x_130);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_134);
x_90 = x_124;
x_91 = x_116;
x_92 = x_112;
x_93 = x_129;
x_94 = x_118;
x_95 = x_115;
x_96 = x_114;
x_97 = x_135;
x_98 = x_110;
x_99 = x_111;
x_100 = x_113;
goto block_109;
}
}
else
{
lean_object* x_136; 
lean_dec(x_130);
x_136 = lean_box(0);
x_90 = x_124;
x_91 = x_116;
x_92 = x_112;
x_93 = x_129;
x_94 = x_118;
x_95 = x_115;
x_96 = x_114;
x_97 = x_136;
x_98 = x_110;
x_99 = x_111;
x_100 = x_113;
goto block_109;
}
}
}
else
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; 
lean_dec(x_124);
lean_dec(x_118);
x_137 = lean_unsigned_to_nat(5u);
x_138 = l_Lean_Syntax_getArg(x_1, x_137);
x_139 = l_Lean_Syntax_isNone(x_138);
if (x_139 == 0)
{
uint8_t x_140; 
lean_inc(x_138);
x_140 = l_Lean_Syntax_matchesNull(x_138, x_116);
if (x_140 == 0)
{
lean_object* x_141; 
lean_dec(x_138);
lean_dec(x_117);
lean_dec(x_115);
lean_dec(x_112);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_141 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_110, x_111, x_113);
lean_dec(x_111);
lean_dec(x_110);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; 
x_142 = l_Lean_Syntax_getArg(x_138, x_114);
lean_dec(x_138);
x_143 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_143, 0, x_142);
x_41 = x_117;
x_42 = x_115;
x_43 = x_112;
x_44 = x_116;
x_45 = x_114;
x_46 = x_143;
x_47 = x_110;
x_48 = x_111;
x_49 = x_113;
goto block_58;
}
}
else
{
lean_object* x_144; 
lean_dec(x_138);
x_144 = lean_box(0);
x_41 = x_117;
x_42 = x_115;
x_43 = x_112;
x_44 = x_116;
x_45 = x_114;
x_46 = x_144;
x_47 = x_110;
x_48 = x_111;
x_49 = x_113;
goto block_58;
}
}
}
}
block_165:
{
lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_150 = lean_unsigned_to_nat(1u);
x_151 = l_Lean_Syntax_getArg(x_1, x_150);
x_152 = l_Lean_Syntax_isNone(x_151);
if (x_152 == 0)
{
uint8_t x_153; 
lean_inc(x_151);
x_153 = l_Lean_Syntax_matchesNull(x_151, x_150);
if (x_153 == 0)
{
lean_object* x_154; 
lean_dec(x_151);
lean_dec(x_146);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_154 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_147, x_148, x_149);
lean_dec(x_148);
lean_dec(x_147);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_155 = l_Lean_Syntax_getArg(x_151, x_12);
lean_dec(x_151);
x_156 = lean_mk_string_unchecked("Term", 4, 4);
x_157 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
x_158 = l_Lean_Name_mkStr4(x_5, x_6, x_156, x_157);
lean_inc(x_155);
x_159 = l_Lean_Syntax_isOfKind(x_155, x_158);
lean_dec(x_158);
if (x_159 == 0)
{
lean_object* x_160; 
lean_dec(x_155);
lean_dec(x_146);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_160 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_147, x_148, x_149);
lean_dec(x_148);
lean_dec(x_147);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = l_Lean_Syntax_getArg(x_155, x_150);
lean_dec(x_155);
x_162 = l_Lean_Syntax_getArgs(x_161);
lean_dec(x_161);
x_163 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_163, 0, x_162);
x_110 = x_147;
x_111 = x_148;
x_112 = x_146;
x_113 = x_149;
x_114 = x_150;
x_115 = x_163;
goto block_145;
}
}
}
else
{
lean_object* x_164; 
lean_dec(x_151);
x_164 = lean_box(0);
x_110 = x_147;
x_111 = x_148;
x_112 = x_146;
x_113 = x_149;
x_114 = x_150;
x_115 = x_164;
goto block_145;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElabRules___lam__1), 4, 0);
x_6 = l_Lean_Elab_Command_adaptExpander(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Elab_Command_elabElabRules___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_7);
return x_17;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabElabRules__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Command", 7, 7);
x_6 = lean_mk_string_unchecked("elab_rules", 10, 10);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("elabElabRules", 13, 13);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElabRules), 4, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Command", 7, 7);
x_5 = lean_mk_string_unchecked("elabElabRules", 13, 13);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(74u);
x_8 = lean_unsigned_to_nat(37u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(81u);
x_11 = lean_unsigned_to_nat(32u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(41u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(54u);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabElab_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_2, x_1);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_uget(x_3, x_2);
lean_inc(x_4);
x_10 = l_Lean_Elab_Command_expandMacroArg(x_9, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = lean_array_uset(x_3, x_2, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_add(x_2, x_16);
x_18 = lean_array_uset(x_14, x_2, x_11);
x_2 = x_17;
x_3 = x_18;
x_6 = x_12;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_4);
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
return x_10;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_10);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; size_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; size_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; size_t x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; size_t x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("Parser", 6, 6);
x_49 = lean_mk_string_unchecked("Command", 7, 7);
x_126 = lean_mk_string_unchecked("elab", 4, 4);
lean_inc(x_49);
lean_inc(x_6);
lean_inc(x_5);
x_127 = l_Lean_Name_mkStr4(x_5, x_6, x_49, x_126);
lean_inc(x_1);
x_128 = l_Lean_Syntax_isOfKind(x_1, x_127);
lean_dec(x_127);
if (x_128 == 0)
{
lean_object* x_250; 
lean_dec(x_49);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_250 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_250;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_449; uint8_t x_450; 
x_251 = lean_unsigned_to_nat(0u);
x_449 = l_Lean_Syntax_getArg(x_1, x_251);
x_450 = l_Lean_Syntax_isNone(x_449);
if (x_450 == 0)
{
lean_object* x_451; uint8_t x_452; 
x_451 = lean_unsigned_to_nat(1u);
lean_inc(x_449);
x_452 = l_Lean_Syntax_matchesNull(x_449, x_451);
if (x_452 == 0)
{
lean_object* x_453; 
lean_dec(x_449);
lean_dec(x_49);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_453 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_453;
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; uint8_t x_457; 
x_454 = l_Lean_Syntax_getArg(x_449, x_251);
lean_dec(x_449);
x_455 = lean_mk_string_unchecked("docComment", 10, 10);
lean_inc(x_49);
lean_inc(x_6);
lean_inc(x_5);
x_456 = l_Lean_Name_mkStr4(x_5, x_6, x_49, x_455);
lean_inc(x_454);
x_457 = l_Lean_Syntax_isOfKind(x_454, x_456);
lean_dec(x_456);
if (x_457 == 0)
{
lean_object* x_458; 
lean_dec(x_454);
lean_dec(x_49);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_458 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_458;
}
else
{
lean_object* x_459; 
x_459 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_459, 0, x_454);
x_429 = x_459;
x_430 = x_2;
x_431 = x_3;
x_432 = x_4;
goto block_448;
}
}
}
else
{
lean_object* x_460; 
lean_dec(x_449);
x_460 = lean_box(0);
x_429 = x_460;
x_430 = x_2;
x_431 = x_3;
x_432 = x_4;
goto block_448;
}
block_313:
{
lean_object* x_270; lean_object* x_271; 
x_270 = lean_alloc_closure((void*)(l_Lean_evalOptPrio___boxed), 3, 1);
lean_closure_set(x_270, 0, x_264);
x_271 = l_Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1(lean_box(0), x_270, x_267, x_268, x_269);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; size_t x_275; size_t x_276; lean_object* x_277; 
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
lean_dec(x_271);
x_274 = l_Lean_Syntax_getArgs(x_252);
lean_dec(x_252);
x_275 = lean_array_size(x_274);
x_276 = lean_usize_of_nat(x_251);
lean_inc(x_267);
x_277 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabElab_spec__0(x_275, x_276, x_274, x_267, x_268, x_273);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_277, 1);
lean_inc(x_279);
lean_dec(x_277);
x_280 = l_Array_unzip___redArg(x_278);
lean_dec(x_278);
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_280, 1);
lean_inc(x_282);
lean_dec(x_280);
x_283 = l_Lean_Syntax_getArg(x_253, x_258);
x_284 = l_Lean_Syntax_getArg(x_1, x_261);
lean_dec(x_1);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_285 = l_Lean_Syntax_getArg(x_253, x_257);
lean_dec(x_253);
x_286 = l_Lean_Syntax_getId(x_285);
lean_dec(x_285);
x_287 = lean_mk_string_unchecked("null", 4, 4);
x_288 = l_Lean_Name_mkStr1(x_287);
x_289 = lean_box(2);
lean_inc(x_281);
x_290 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_288);
lean_ctor_set(x_290, 2, x_281);
x_291 = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkNameFromParserSyntax___boxed), 4, 2);
lean_closure_set(x_291, 0, x_286);
lean_closure_set(x_291, 1, x_290);
x_292 = l_Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1(lean_box(0), x_291, x_267, x_268, x_279);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_292, 1);
lean_inc(x_294);
lean_dec(x_292);
lean_inc(x_263);
x_295 = l_Lean_Elab_Command_addMacroScopeIfLocal___at___Lean_Elab_Command_elabSyntax_spec__1(x_293, x_263, x_267, x_268, x_294);
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_295, 1);
lean_inc(x_297);
lean_dec(x_295);
lean_inc(x_296);
x_298 = l_Lean_mkIdentFrom(x_284, x_296, x_128);
x_205 = x_283;
x_206 = x_272;
x_207 = x_254;
x_208 = x_255;
x_209 = x_282;
x_210 = x_256;
x_211 = x_266;
x_212 = x_260;
x_213 = x_268;
x_214 = x_297;
x_215 = x_296;
x_216 = x_262;
x_217 = x_263;
x_218 = x_281;
x_219 = x_284;
x_220 = x_276;
x_221 = x_267;
x_222 = x_265;
x_223 = x_298;
goto block_249;
}
else
{
uint8_t x_299; 
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_282);
lean_dec(x_281);
lean_dec(x_272);
lean_dec(x_268);
lean_dec(x_267);
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_260);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_49);
lean_dec(x_6);
lean_dec(x_5);
x_299 = !lean_is_exclusive(x_292);
if (x_299 == 0)
{
return x_292;
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_300 = lean_ctor_get(x_292, 0);
x_301 = lean_ctor_get(x_292, 1);
lean_inc(x_301);
lean_inc(x_300);
lean_dec(x_292);
x_302 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_302, 0, x_300);
lean_ctor_set(x_302, 1, x_301);
return x_302;
}
}
}
else
{
lean_object* x_303; lean_object* x_304; 
lean_dec(x_253);
x_303 = lean_ctor_get(x_259, 0);
lean_inc(x_303);
lean_dec(x_259);
x_304 = l_Lean_Syntax_getId(x_303);
x_205 = x_283;
x_206 = x_272;
x_207 = x_254;
x_208 = x_255;
x_209 = x_282;
x_210 = x_256;
x_211 = x_266;
x_212 = x_260;
x_213 = x_268;
x_214 = x_279;
x_215 = x_304;
x_216 = x_262;
x_217 = x_263;
x_218 = x_281;
x_219 = x_284;
x_220 = x_276;
x_221 = x_267;
x_222 = x_265;
x_223 = x_303;
goto block_249;
}
}
else
{
uint8_t x_305; 
lean_dec(x_272);
lean_dec(x_268);
lean_dec(x_267);
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_253);
lean_dec(x_49);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_305 = !lean_is_exclusive(x_277);
if (x_305 == 0)
{
return x_277;
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_306 = lean_ctor_get(x_277, 0);
x_307 = lean_ctor_get(x_277, 1);
lean_inc(x_307);
lean_inc(x_306);
lean_dec(x_277);
x_308 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set(x_308, 1, x_307);
return x_308;
}
}
}
else
{
uint8_t x_309; 
lean_dec(x_268);
lean_dec(x_267);
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_49);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_309 = !lean_is_exclusive(x_271);
if (x_309 == 0)
{
return x_271;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_310 = lean_ctor_get(x_271, 0);
x_311 = lean_ctor_get(x_271, 1);
lean_inc(x_311);
lean_inc(x_310);
lean_dec(x_271);
x_312 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_312, 0, x_310);
lean_ctor_set(x_312, 1, x_311);
return x_312;
}
}
}
block_345:
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; uint8_t x_333; 
x_329 = lean_unsigned_to_nat(8u);
x_330 = l_Lean_Syntax_getArg(x_1, x_329);
x_331 = lean_mk_string_unchecked("elabTail", 8, 8);
lean_inc(x_49);
lean_inc(x_6);
lean_inc(x_5);
x_332 = l_Lean_Name_mkStr4(x_5, x_6, x_49, x_331);
lean_inc(x_330);
x_333 = l_Lean_Syntax_isOfKind(x_330, x_332);
lean_dec(x_332);
if (x_333 == 0)
{
lean_object* x_334; 
lean_dec(x_330);
lean_dec(x_325);
lean_dec(x_323);
lean_dec(x_322);
lean_dec(x_318);
lean_dec(x_317);
lean_dec(x_316);
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_49);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_334 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_326, x_327, x_328);
lean_dec(x_327);
lean_dec(x_326);
return x_334;
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; 
x_335 = lean_unsigned_to_nat(7u);
x_336 = l_Lean_Syntax_getArg(x_1, x_335);
x_337 = l_Lean_Syntax_getArg(x_330, x_320);
x_338 = l_Lean_Syntax_getArg(x_330, x_321);
x_339 = l_Lean_Syntax_isNone(x_338);
if (x_339 == 0)
{
uint8_t x_340; 
lean_inc(x_338);
x_340 = l_Lean_Syntax_matchesNull(x_338, x_321);
if (x_340 == 0)
{
lean_object* x_341; 
lean_dec(x_338);
lean_dec(x_337);
lean_dec(x_336);
lean_dec(x_330);
lean_dec(x_325);
lean_dec(x_323);
lean_dec(x_322);
lean_dec(x_318);
lean_dec(x_317);
lean_dec(x_316);
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_49);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_341 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_326, x_327, x_328);
lean_dec(x_327);
lean_dec(x_326);
return x_341;
}
else
{
lean_object* x_342; lean_object* x_343; 
x_342 = l_Lean_Syntax_getArg(x_338, x_320);
lean_dec(x_338);
x_343 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_343, 0, x_342);
x_252 = x_336;
x_253 = x_330;
x_254 = x_316;
x_255 = x_317;
x_256 = x_318;
x_257 = x_320;
x_258 = x_319;
x_259 = x_322;
x_260 = x_323;
x_261 = x_324;
x_262 = x_314;
x_263 = x_315;
x_264 = x_325;
x_265 = x_337;
x_266 = x_343;
x_267 = x_326;
x_268 = x_327;
x_269 = x_328;
goto block_313;
}
}
else
{
lean_object* x_344; 
lean_dec(x_338);
x_344 = lean_box(0);
x_252 = x_336;
x_253 = x_330;
x_254 = x_316;
x_255 = x_317;
x_256 = x_318;
x_257 = x_320;
x_258 = x_319;
x_259 = x_322;
x_260 = x_323;
x_261 = x_324;
x_262 = x_314;
x_263 = x_315;
x_264 = x_325;
x_265 = x_337;
x_266 = x_344;
x_267 = x_326;
x_268 = x_327;
x_269 = x_328;
goto block_313;
}
}
}
block_373:
{
lean_object* x_360; lean_object* x_361; uint8_t x_362; 
x_360 = lean_unsigned_to_nat(6u);
x_361 = l_Lean_Syntax_getArg(x_1, x_360);
x_362 = l_Lean_Syntax_isNone(x_361);
if (x_362 == 0)
{
uint8_t x_363; 
lean_inc(x_361);
x_363 = l_Lean_Syntax_matchesNull(x_361, x_351);
if (x_363 == 0)
{
lean_object* x_364; 
lean_dec(x_361);
lean_dec(x_356);
lean_dec(x_354);
lean_dec(x_350);
lean_dec(x_349);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_49);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_364 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_357, x_358, x_359);
lean_dec(x_358);
lean_dec(x_357);
return x_364;
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; 
x_365 = l_Lean_Syntax_getArg(x_361, x_251);
lean_dec(x_361);
x_366 = lean_mk_string_unchecked("namedPrio", 9, 9);
lean_inc(x_49);
lean_inc(x_6);
lean_inc(x_5);
x_367 = l_Lean_Name_mkStr4(x_5, x_6, x_49, x_366);
lean_inc(x_365);
x_368 = l_Lean_Syntax_isOfKind(x_365, x_367);
lean_dec(x_367);
if (x_368 == 0)
{
lean_object* x_369; 
lean_dec(x_365);
lean_dec(x_356);
lean_dec(x_354);
lean_dec(x_350);
lean_dec(x_349);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_49);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_369 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_357, x_358, x_359);
lean_dec(x_358);
lean_dec(x_357);
return x_369;
}
else
{
lean_object* x_370; lean_object* x_371; 
x_370 = l_Lean_Syntax_getArg(x_365, x_355);
lean_dec(x_365);
x_371 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_371, 0, x_370);
x_314 = x_346;
x_315 = x_347;
x_316 = x_348;
x_317 = x_349;
x_318 = x_350;
x_319 = x_352;
x_320 = x_351;
x_321 = x_353;
x_322 = x_356;
x_323 = x_354;
x_324 = x_355;
x_325 = x_371;
x_326 = x_357;
x_327 = x_358;
x_328 = x_359;
goto block_345;
}
}
}
else
{
lean_object* x_372; 
lean_dec(x_361);
x_372 = lean_box(0);
x_314 = x_346;
x_315 = x_347;
x_316 = x_348;
x_317 = x_349;
x_318 = x_350;
x_319 = x_352;
x_320 = x_351;
x_321 = x_353;
x_322 = x_356;
x_323 = x_354;
x_324 = x_355;
x_325 = x_372;
x_326 = x_357;
x_327 = x_358;
x_328 = x_359;
goto block_345;
}
}
block_400:
{
lean_object* x_387; lean_object* x_388; uint8_t x_389; 
x_387 = lean_unsigned_to_nat(5u);
x_388 = l_Lean_Syntax_getArg(x_1, x_387);
x_389 = l_Lean_Syntax_isNone(x_388);
if (x_389 == 0)
{
uint8_t x_390; 
lean_inc(x_388);
x_390 = l_Lean_Syntax_matchesNull(x_388, x_379);
if (x_390 == 0)
{
lean_object* x_391; 
lean_dec(x_388);
lean_dec(x_383);
lean_dec(x_381);
lean_dec(x_377);
lean_dec(x_376);
lean_dec(x_375);
lean_dec(x_374);
lean_dec(x_49);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_391 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_384, x_385, x_386);
lean_dec(x_385);
lean_dec(x_384);
return x_391;
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; uint8_t x_395; 
x_392 = l_Lean_Syntax_getArg(x_388, x_251);
lean_dec(x_388);
x_393 = lean_mk_string_unchecked("namedName", 9, 9);
lean_inc(x_49);
lean_inc(x_6);
lean_inc(x_5);
x_394 = l_Lean_Name_mkStr4(x_5, x_6, x_49, x_393);
lean_inc(x_392);
x_395 = l_Lean_Syntax_isOfKind(x_392, x_394);
lean_dec(x_394);
if (x_395 == 0)
{
lean_object* x_396; 
lean_dec(x_392);
lean_dec(x_383);
lean_dec(x_381);
lean_dec(x_377);
lean_dec(x_376);
lean_dec(x_375);
lean_dec(x_374);
lean_dec(x_49);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_396 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_384, x_385, x_386);
lean_dec(x_385);
lean_dec(x_384);
return x_396;
}
else
{
lean_object* x_397; lean_object* x_398; 
x_397 = l_Lean_Syntax_getArg(x_392, x_382);
lean_dec(x_392);
x_398 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_398, 0, x_397);
x_346 = x_374;
x_347 = x_375;
x_348 = x_376;
x_349 = x_377;
x_350 = x_383;
x_351 = x_379;
x_352 = x_378;
x_353 = x_380;
x_354 = x_381;
x_355 = x_382;
x_356 = x_398;
x_357 = x_384;
x_358 = x_385;
x_359 = x_386;
goto block_373;
}
}
}
else
{
lean_object* x_399; 
lean_dec(x_388);
x_399 = lean_box(0);
x_346 = x_374;
x_347 = x_375;
x_348 = x_376;
x_349 = x_377;
x_350 = x_383;
x_351 = x_379;
x_352 = x_378;
x_353 = x_380;
x_354 = x_381;
x_355 = x_382;
x_356 = x_399;
x_357 = x_384;
x_358 = x_385;
x_359 = x_386;
goto block_373;
}
}
block_428:
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; uint8_t x_412; 
x_407 = lean_unsigned_to_nat(2u);
x_408 = l_Lean_Syntax_getArg(x_1, x_407);
x_409 = lean_mk_string_unchecked("Term", 4, 4);
x_410 = lean_mk_string_unchecked("attrKind", 8, 8);
lean_inc(x_409);
lean_inc(x_6);
lean_inc(x_5);
x_411 = l_Lean_Name_mkStr4(x_5, x_6, x_409, x_410);
lean_inc(x_408);
x_412 = l_Lean_Syntax_isOfKind(x_408, x_411);
if (x_412 == 0)
{
lean_object* x_413; 
lean_dec(x_411);
lean_dec(x_409);
lean_dec(x_408);
lean_dec(x_403);
lean_dec(x_401);
lean_dec(x_49);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_413 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_404, x_405, x_406);
lean_dec(x_405);
lean_dec(x_404);
return x_413;
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; uint8_t x_417; 
x_414 = lean_unsigned_to_nat(3u);
x_415 = lean_unsigned_to_nat(4u);
x_416 = l_Lean_Syntax_getArg(x_1, x_415);
x_417 = l_Lean_Syntax_isNone(x_416);
if (x_417 == 0)
{
uint8_t x_418; 
lean_inc(x_416);
x_418 = l_Lean_Syntax_matchesNull(x_416, x_402);
if (x_418 == 0)
{
lean_object* x_419; 
lean_dec(x_416);
lean_dec(x_411);
lean_dec(x_409);
lean_dec(x_408);
lean_dec(x_403);
lean_dec(x_401);
lean_dec(x_49);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_419 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_404, x_405, x_406);
lean_dec(x_405);
lean_dec(x_404);
return x_419;
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; uint8_t x_423; 
x_420 = l_Lean_Syntax_getArg(x_416, x_251);
lean_dec(x_416);
x_421 = lean_mk_string_unchecked("precedence", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
x_422 = l_Lean_Name_mkStr3(x_5, x_6, x_421);
lean_inc(x_420);
x_423 = l_Lean_Syntax_isOfKind(x_420, x_422);
lean_dec(x_422);
if (x_423 == 0)
{
lean_object* x_424; 
lean_dec(x_420);
lean_dec(x_411);
lean_dec(x_409);
lean_dec(x_408);
lean_dec(x_403);
lean_dec(x_401);
lean_dec(x_49);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_424 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_404, x_405, x_406);
lean_dec(x_405);
lean_dec(x_404);
return x_424;
}
else
{
lean_object* x_425; lean_object* x_426; 
x_425 = l_Lean_Syntax_getArg(x_420, x_402);
lean_dec(x_420);
x_426 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_426, 0, x_425);
x_374 = x_403;
x_375 = x_408;
x_376 = x_401;
x_377 = x_409;
x_378 = x_415;
x_379 = x_402;
x_380 = x_407;
x_381 = x_411;
x_382 = x_414;
x_383 = x_426;
x_384 = x_404;
x_385 = x_405;
x_386 = x_406;
goto block_400;
}
}
}
else
{
lean_object* x_427; 
lean_dec(x_416);
x_427 = lean_box(0);
x_374 = x_403;
x_375 = x_408;
x_376 = x_401;
x_377 = x_409;
x_378 = x_415;
x_379 = x_402;
x_380 = x_407;
x_381 = x_411;
x_382 = x_414;
x_383 = x_427;
x_384 = x_404;
x_385 = x_405;
x_386 = x_406;
goto block_400;
}
}
}
block_448:
{
lean_object* x_433; lean_object* x_434; uint8_t x_435; 
x_433 = lean_unsigned_to_nat(1u);
x_434 = l_Lean_Syntax_getArg(x_1, x_433);
x_435 = l_Lean_Syntax_isNone(x_434);
if (x_435 == 0)
{
uint8_t x_436; 
lean_inc(x_434);
x_436 = l_Lean_Syntax_matchesNull(x_434, x_433);
if (x_436 == 0)
{
lean_object* x_437; 
lean_dec(x_434);
lean_dec(x_429);
lean_dec(x_49);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_437 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_430, x_431, x_432);
lean_dec(x_431);
lean_dec(x_430);
return x_437;
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; 
x_438 = l_Lean_Syntax_getArg(x_434, x_251);
lean_dec(x_434);
x_439 = lean_mk_string_unchecked("Term", 4, 4);
x_440 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
x_441 = l_Lean_Name_mkStr4(x_5, x_6, x_439, x_440);
lean_inc(x_438);
x_442 = l_Lean_Syntax_isOfKind(x_438, x_441);
lean_dec(x_441);
if (x_442 == 0)
{
lean_object* x_443; 
lean_dec(x_438);
lean_dec(x_429);
lean_dec(x_49);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_443 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_430, x_431, x_432);
lean_dec(x_431);
lean_dec(x_430);
return x_443;
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_444 = l_Lean_Syntax_getArg(x_438, x_433);
lean_dec(x_438);
x_445 = l_Lean_Syntax_getArgs(x_444);
lean_dec(x_444);
x_446 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_446, 0, x_445);
x_401 = x_429;
x_402 = x_433;
x_403 = x_446;
x_404 = x_430;
x_405 = x_431;
x_406 = x_432;
goto block_428;
}
}
}
else
{
lean_object* x_447; 
lean_dec(x_434);
x_447 = lean_box(0);
x_401 = x_429;
x_402 = x_433;
x_403 = x_447;
x_404 = x_430;
x_405 = x_431;
x_406 = x_432;
goto block_428;
}
}
}
block_48:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_25 = l_Array_append(lean_box(0), x_16, x_24);
lean_dec(x_24);
lean_inc(x_21);
lean_inc(x_10);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_10);
lean_ctor_set(x_26, 1, x_21);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_mk_string_unchecked("matchAlts", 9, 9);
lean_inc(x_11);
lean_inc(x_6);
lean_inc(x_5);
x_28 = l_Lean_Name_mkStr4(x_5, x_6, x_11, x_27);
x_29 = lean_mk_string_unchecked("matchAlt", 8, 8);
lean_inc(x_11);
lean_inc(x_6);
lean_inc(x_5);
x_30 = l_Lean_Name_mkStr4(x_5, x_6, x_11, x_29);
x_31 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_10);
x_32 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_32, 0, x_10);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_mk_string_unchecked("quot", 4, 4);
x_34 = l_Lean_Name_mkStr4(x_5, x_6, x_11, x_33);
x_35 = lean_mk_string_unchecked("`(", 2, 2);
lean_inc(x_10);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_10);
lean_ctor_set(x_36, 1, x_35);
lean_inc(x_10);
x_37 = l_Lean_Syntax_node3(x_10, x_34, x_36, x_7, x_12);
lean_inc(x_21);
lean_inc(x_10);
x_38 = l_Lean_Syntax_node1(x_10, x_21, x_37);
lean_inc(x_21);
lean_inc(x_10);
x_39 = l_Lean_Syntax_node1(x_10, x_21, x_38);
x_40 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_10);
x_41 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_41, 0, x_10);
lean_ctor_set(x_41, 1, x_40);
lean_inc(x_10);
x_42 = l_Lean_Syntax_node4(x_10, x_30, x_32, x_39, x_41, x_9);
lean_inc(x_21);
lean_inc(x_10);
x_43 = l_Lean_Syntax_node1(x_10, x_21, x_42);
lean_inc(x_10);
x_44 = l_Lean_Syntax_node1(x_10, x_28, x_43);
lean_inc(x_17);
lean_inc(x_10);
x_45 = l_Lean_Syntax_node8(x_10, x_22, x_13, x_17, x_23, x_14, x_17, x_18, x_26, x_44);
x_46 = l_Lean_Syntax_node2(x_10, x_21, x_8, x_45);
x_47 = l_Lean_Elab_Command_elabCommand(x_46, x_20, x_15, x_19);
return x_47;
}
block_125:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; size_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_inc(x_62);
x_73 = l_Array_append(lean_box(0), x_62, x_72);
lean_dec(x_72);
lean_inc(x_71);
lean_inc(x_53);
x_74 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_74, 0, x_53);
lean_ctor_set(x_74, 1, x_71);
lean_ctor_set(x_74, 2, x_73);
x_75 = lean_mk_string_unchecked("namedName", 9, 9);
lean_inc(x_49);
lean_inc(x_6);
lean_inc(x_5);
x_76 = l_Lean_Name_mkStr4(x_5, x_6, x_49, x_75);
x_77 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_53);
x_78 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_78, 0, x_53);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_mk_string_unchecked("name", 4, 4);
lean_inc(x_53);
x_80 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_80, 0, x_53);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_53);
x_82 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_82, 0, x_53);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_53);
x_84 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_84, 0, x_53);
lean_ctor_set(x_84, 1, x_83);
lean_inc(x_84);
lean_inc(x_82);
lean_inc(x_78);
lean_inc(x_53);
x_85 = l_Lean_Syntax_node5(x_53, x_76, x_78, x_80, x_82, x_64, x_84);
lean_inc(x_71);
lean_inc(x_53);
x_86 = l_Lean_Syntax_node1(x_53, x_71, x_85);
x_87 = lean_mk_string_unchecked("namedPrio", 9, 9);
lean_inc(x_49);
lean_inc(x_6);
lean_inc(x_5);
x_88 = l_Lean_Name_mkStr4(x_5, x_6, x_49, x_87);
x_89 = lean_mk_string_unchecked("priority", 8, 8);
lean_inc(x_53);
x_90 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_90, 0, x_53);
lean_ctor_set(x_90, 1, x_89);
x_91 = l___private_Init_Data_Repr_0__Nat_reprFast(x_54);
x_92 = l_Lean_Syntax_mkNumLit(x_91, x_69);
lean_inc(x_84);
lean_inc(x_53);
x_93 = l_Lean_Syntax_node5(x_53, x_88, x_78, x_90, x_82, x_92, x_84);
lean_inc(x_71);
lean_inc(x_53);
x_94 = l_Lean_Syntax_node1(x_53, x_71, x_93);
x_95 = lean_array_size(x_65);
x_96 = l_Array_mapMUnsafe_map___at___Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(x_95, x_67, x_65);
lean_inc(x_62);
x_97 = l_Array_append(lean_box(0), x_62, x_96);
lean_dec(x_96);
lean_inc(x_71);
lean_inc(x_53);
x_98 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_98, 0, x_53);
lean_ctor_set(x_98, 1, x_71);
lean_ctor_set(x_98, 2, x_97);
x_99 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_53);
x_100 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_100, 0, x_53);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_unsigned_to_nat(10u);
x_102 = lean_mk_empty_array_with_capacity(x_101);
lean_inc(x_57);
x_103 = lean_array_push(x_102, x_57);
x_104 = lean_array_push(x_103, x_59);
x_105 = lean_array_push(x_104, x_63);
x_106 = lean_array_push(x_105, x_51);
x_107 = lean_array_push(x_106, x_74);
x_108 = lean_array_push(x_107, x_86);
x_109 = lean_array_push(x_108, x_94);
x_110 = lean_array_push(x_109, x_98);
lean_inc(x_100);
x_111 = lean_array_push(x_110, x_100);
lean_inc(x_70);
x_112 = lean_array_push(x_111, x_70);
lean_inc(x_53);
x_113 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_113, 0, x_53);
lean_ctor_set(x_113, 1, x_61);
lean_ctor_set(x_113, 2, x_112);
x_114 = lean_mk_string_unchecked("elab_rules", 10, 10);
lean_inc(x_114);
lean_inc(x_6);
lean_inc(x_5);
x_115 = l_Lean_Name_mkStr4(x_5, x_6, x_49, x_114);
lean_inc(x_62);
lean_inc(x_71);
lean_inc(x_53);
x_116 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_116, 0, x_53);
lean_ctor_set(x_116, 1, x_71);
lean_ctor_set(x_116, 2, x_62);
lean_inc(x_116);
lean_inc(x_53);
x_117 = l_Lean_Syntax_node1(x_53, x_58, x_116);
lean_inc(x_53);
x_118 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_118, 0, x_53);
lean_ctor_set(x_118, 1, x_114);
lean_inc(x_71);
lean_inc(x_53);
x_119 = l_Lean_Syntax_node2(x_53, x_71, x_100, x_70);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_120; 
x_120 = l_Array_empty(lean_box(0));
x_7 = x_50;
x_8 = x_113;
x_9 = x_52;
x_10 = x_53;
x_11 = x_55;
x_12 = x_84;
x_13 = x_57;
x_14 = x_118;
x_15 = x_60;
x_16 = x_62;
x_17 = x_116;
x_18 = x_119;
x_19 = x_66;
x_20 = x_68;
x_21 = x_71;
x_22 = x_115;
x_23 = x_117;
x_24 = x_120;
goto block_48;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_56, 0);
lean_inc(x_121);
lean_dec(x_56);
x_122 = lean_mk_string_unchecked("<=", 2, 2);
lean_inc(x_53);
x_123 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_123, 0, x_53);
lean_ctor_set(x_123, 1, x_122);
x_124 = l_Array_mkArray2(lean_box(0), x_123, x_121);
x_7 = x_50;
x_8 = x_113;
x_9 = x_52;
x_10 = x_53;
x_11 = x_55;
x_12 = x_84;
x_13 = x_57;
x_14 = x_118;
x_15 = x_60;
x_16 = x_62;
x_17 = x_116;
x_18 = x_119;
x_19 = x_66;
x_20 = x_68;
x_21 = x_71;
x_22 = x_115;
x_23 = x_117;
x_24 = x_124;
goto block_48;
}
}
block_165:
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_inc(x_141);
x_153 = l_Array_append(lean_box(0), x_141, x_152);
lean_dec(x_152);
lean_inc(x_151);
lean_inc(x_131);
x_154 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_154, 0, x_131);
lean_ctor_set(x_154, 1, x_151);
lean_ctor_set(x_154, 2, x_153);
x_155 = l_Lean_SourceInfo_fromRef(x_145, x_128);
lean_dec(x_145);
x_156 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_133);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_157; 
x_157 = l_Array_empty(lean_box(0));
x_50 = x_129;
x_51 = x_156;
x_52 = x_130;
x_53 = x_131;
x_54 = x_132;
x_55 = x_134;
x_56 = x_136;
x_57 = x_137;
x_58 = x_138;
x_59 = x_154;
x_60 = x_139;
x_61 = x_140;
x_62 = x_141;
x_63 = x_142;
x_64 = x_144;
x_65 = x_143;
x_66 = x_147;
x_67 = x_146;
x_68 = x_149;
x_69 = x_148;
x_70 = x_150;
x_71 = x_151;
x_72 = x_157;
goto block_125;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_158 = lean_ctor_get(x_135, 0);
lean_inc(x_158);
lean_dec(x_135);
x_159 = lean_mk_string_unchecked("precedence", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
x_160 = l_Lean_Name_mkStr3(x_5, x_6, x_159);
x_161 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_131);
x_162 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_162, 0, x_131);
lean_ctor_set(x_162, 1, x_161);
lean_inc(x_131);
x_163 = l_Lean_Syntax_node2(x_131, x_160, x_162, x_158);
x_164 = l_Array_mkArray1___redArg(x_163);
x_50 = x_129;
x_51 = x_156;
x_52 = x_130;
x_53 = x_131;
x_54 = x_132;
x_55 = x_134;
x_56 = x_136;
x_57 = x_137;
x_58 = x_138;
x_59 = x_154;
x_60 = x_139;
x_61 = x_140;
x_62 = x_141;
x_63 = x_142;
x_64 = x_144;
x_65 = x_143;
x_66 = x_147;
x_67 = x_146;
x_68 = x_149;
x_69 = x_148;
x_70 = x_150;
x_71 = x_151;
x_72 = x_164;
goto block_125;
}
}
block_204:
{
lean_object* x_190; lean_object* x_191; 
lean_inc(x_178);
x_190 = l_Array_append(lean_box(0), x_178, x_189);
lean_dec(x_189);
lean_inc(x_188);
lean_inc(x_168);
x_191 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_191, 0, x_168);
lean_ctor_set(x_191, 1, x_188);
lean_ctor_set(x_191, 2, x_190);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_192; 
x_192 = l_Array_empty(lean_box(0));
x_129 = x_166;
x_130 = x_167;
x_131 = x_168;
x_132 = x_169;
x_133 = x_170;
x_134 = x_171;
x_135 = x_172;
x_136 = x_173;
x_137 = x_191;
x_138 = x_174;
x_139 = x_175;
x_140 = x_176;
x_141 = x_178;
x_142 = x_179;
x_143 = x_181;
x_144 = x_180;
x_145 = x_182;
x_146 = x_184;
x_147 = x_183;
x_148 = x_186;
x_149 = x_185;
x_150 = x_187;
x_151 = x_188;
x_152 = x_192;
goto block_165;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_193 = lean_ctor_get(x_177, 0);
lean_inc(x_193);
lean_dec(x_177);
x_194 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_171);
lean_inc(x_6);
lean_inc(x_5);
x_195 = l_Lean_Name_mkStr4(x_5, x_6, x_171, x_194);
x_196 = lean_mk_string_unchecked("@[", 2, 2);
lean_inc(x_168);
x_197 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_197, 0, x_168);
lean_ctor_set(x_197, 1, x_196);
lean_inc(x_178);
x_198 = l_Array_append(lean_box(0), x_178, x_193);
lean_dec(x_193);
lean_inc(x_188);
lean_inc(x_168);
x_199 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_199, 0, x_168);
lean_ctor_set(x_199, 1, x_188);
lean_ctor_set(x_199, 2, x_198);
x_200 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_168);
x_201 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_201, 0, x_168);
lean_ctor_set(x_201, 1, x_200);
lean_inc(x_168);
x_202 = l_Lean_Syntax_node3(x_168, x_195, x_197, x_199, x_201);
x_203 = l_Array_mkArray1___redArg(x_202);
x_129 = x_166;
x_130 = x_167;
x_131 = x_168;
x_132 = x_169;
x_133 = x_170;
x_134 = x_171;
x_135 = x_172;
x_136 = x_173;
x_137 = x_191;
x_138 = x_174;
x_139 = x_175;
x_140 = x_176;
x_141 = x_178;
x_142 = x_179;
x_143 = x_181;
x_144 = x_180;
x_145 = x_182;
x_146 = x_184;
x_147 = x_183;
x_148 = x_186;
x_149 = x_185;
x_150 = x_187;
x_151 = x_188;
x_152 = x_203;
goto block_165;
}
}
block_249:
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_224 = l_Lean_Elab_Command_getScope___redArg(x_213, x_214);
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
lean_dec(x_224);
x_227 = l_Lean_Elab_Command_getRef(x_221, x_213, x_226);
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
x_230 = l_Lean_Elab_Command_getCurrMacroScope(x_221, x_213, x_229);
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
lean_dec(x_230);
x_232 = l_Lean_Elab_Command_getMainModule___redArg(x_213, x_231);
x_233 = lean_ctor_get(x_232, 1);
lean_inc(x_233);
lean_dec(x_232);
x_234 = lean_ctor_get(x_225, 2);
lean_inc(x_234);
lean_dec(x_225);
x_235 = l_Lean_Name_append(x_234, x_215);
x_236 = lean_box(2);
x_237 = lean_box(0);
x_238 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_235);
lean_ctor_set(x_238, 2, x_209);
x_239 = lean_unbox(x_237);
x_240 = l_Lean_SourceInfo_fromRef(x_228, x_239);
lean_dec(x_228);
x_241 = lean_mk_string_unchecked("null", 4, 4);
x_242 = l_Lean_Name_mkStr1(x_241);
x_243 = lean_mk_string_unchecked("syntax", 6, 6);
lean_inc(x_243);
lean_inc(x_49);
lean_inc(x_6);
lean_inc(x_5);
x_244 = l_Lean_Name_mkStr4(x_5, x_6, x_49, x_243);
x_245 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_246; 
x_246 = l_Array_empty(lean_box(0));
x_166 = x_238;
x_167 = x_205;
x_168 = x_240;
x_169 = x_206;
x_170 = x_243;
x_171 = x_208;
x_172 = x_210;
x_173 = x_211;
x_174 = x_212;
x_175 = x_213;
x_176 = x_244;
x_177 = x_216;
x_178 = x_245;
x_179 = x_217;
x_180 = x_223;
x_181 = x_218;
x_182 = x_219;
x_183 = x_233;
x_184 = x_220;
x_185 = x_221;
x_186 = x_236;
x_187 = x_222;
x_188 = x_242;
x_189 = x_246;
goto block_204;
}
else
{
lean_object* x_247; lean_object* x_248; 
x_247 = lean_ctor_get(x_207, 0);
lean_inc(x_247);
lean_dec(x_207);
x_248 = l_Array_mkArray1___redArg(x_247);
x_166 = x_238;
x_167 = x_205;
x_168 = x_240;
x_169 = x_206;
x_170 = x_243;
x_171 = x_208;
x_172 = x_210;
x_173 = x_211;
x_174 = x_212;
x_175 = x_213;
x_176 = x_244;
x_177 = x_216;
x_178 = x_245;
x_179 = x_217;
x_180 = x_223;
x_181 = x_218;
x_182 = x_219;
x_183 = x_233;
x_184 = x_220;
x_185 = x_221;
x_186 = x_236;
x_187 = x_222;
x_188 = x_242;
x_189 = x_248;
goto block_204;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabElab_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabElab_spec__0(x_7, x_8, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabElab__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Command", 7, 7);
x_6 = lean_mk_string_unchecked("elab", 4, 4);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("elabElab", 8, 8);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElab), 4, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabElab_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Command", 7, 7);
x_5 = lean_mk_string_unchecked("elabElab", 8, 8);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(84u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(100u);
x_11 = lean_unsigned_to_nat(31u);
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
x_16 = lean_unsigned_to_nat(12u);
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
lean_object* initialize_Lean_Elab_MacroArgUtil(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_AuxDef(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_ElabRules(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_MacroArgUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_AuxDef(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabElabRules__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabElab__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabElab_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
