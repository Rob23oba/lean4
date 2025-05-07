// Lean compiler output
// Module: Lake.DSL.Config
// Imports: Lean.Elab.ElabRules Lake.DSL.Extensions Lake.DSL.Syntax
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
lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lake_dirExt;
LEAN_EXPORT lean_object* l_Lake_DSL_elabDirConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lake_DSL_elabGetConfig__1(lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lake_optsExt;
lean_object* l_Lean_NameMap_find_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withMacroExpansion___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_dummyGetConfig_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_dummyGetConfig_x3f___boxed(lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_quoteNameMk(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
LEAN_EXPORT lean_object* l___regBuiltin_Lake_DSL_elabDirConst__1(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_dummyDir;
lean_object* l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_elabGetConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
static lean_object* _init_l_Lake_DSL_dummyDir() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_dummyGetConfig_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_dummyGetConfig_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_DSL_dummyGetConfig_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabDirConst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_18 = lean_box(0);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = l_Lake_dirExt;
x_21 = lean_ctor_get_uint8(x_20, sizeof(void*)*3);
x_22 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_18, x_20, x_19, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_23 = lean_mk_string_unchecked("id", 2, 2);
x_24 = l_Lean_Name_mkStr1(x_23);
x_25 = lean_box(0);
x_26 = lean_unbox(x_25);
x_27 = l_Lean_mkCIdentFrom(x_1, x_24, x_26);
x_28 = lean_mk_string_unchecked("Lake", 4, 4);
x_29 = lean_mk_string_unchecked("DSL", 3, 3);
x_30 = lean_mk_string_unchecked("dummyDir", 8, 8);
x_31 = l_Lean_Name_mkStr3(x_28, x_29, x_30);
x_32 = lean_unbox(x_25);
x_33 = l_Lean_mkCIdentFrom(x_1, x_31, x_32);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_mk_empty_array_with_capacity(x_34);
x_36 = lean_array_push(x_35, x_33);
x_37 = l_Lean_Syntax_mkApp(x_27, x_36);
x_13 = x_37;
goto block_17;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_38 = lean_ctor_get(x_22, 0);
lean_inc(x_38);
lean_dec(x_22);
x_39 = lean_box(0);
x_40 = lean_unbox(x_39);
x_41 = l_Lean_SourceInfo_fromRef(x_1, x_40);
x_42 = lean_mk_string_unchecked("System", 6, 6);
x_43 = lean_mk_string_unchecked("FilePath", 8, 8);
x_44 = lean_mk_string_unchecked("mk", 2, 2);
x_45 = l_Lean_Name_mkStr3(x_42, x_43, x_44);
x_46 = lean_unbox(x_39);
x_47 = l_Lean_mkCIdentFrom(x_1, x_45, x_46);
x_48 = l_Lean_Syntax_mkStrLit(x_38, x_41);
lean_dec(x_38);
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_mk_empty_array_with_capacity(x_49);
x_51 = lean_array_push(x_50, x_48);
x_52 = l_Lean_Syntax_mkApp(x_47, x_51);
x_13 = x_52;
goto block_17;
}
block_17:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_box(1);
lean_inc(x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_14);
lean_closure_set(x_15, 3, x_14);
x_16 = l_Lean_Elab_Term_withMacroExpansion___redArg(x_1, x_13, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lake_DSL_elabDirConst__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = lean_mk_string_unchecked("Lake", 4, 4);
x_4 = lean_mk_string_unchecked("DSL", 3, 3);
x_5 = lean_mk_string_unchecked("dirConst", 8, 8);
lean_inc(x_4);
lean_inc(x_3);
x_6 = l_Lean_Name_mkStr3(x_3, x_4, x_5);
x_7 = lean_mk_string_unchecked("elabDirConst", 12, 12);
x_8 = l_Lean_Name_mkStr3(x_3, x_4, x_7);
x_9 = lean_alloc_closure((void*)(l_Lake_DSL_elabDirConst), 9, 0);
x_10 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_6, x_8, x_9, x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabGetConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_10 = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_mk_string_unchecked("Lake", 4, 4);
x_13 = lean_mk_string_unchecked("DSL", 3, 3);
x_14 = lean_mk_string_unchecked("getConfig", 9, 9);
lean_inc(x_13);
lean_inc(x_12);
x_15 = l_Lean_Name_mkStr3(x_12, x_13, x_14);
lean_inc(x_1);
x_16 = l_Lean_Syntax_isOfKind(x_1, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_24; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_11);
return x_24;
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_st_ref_get(x_8, x_11);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
x_29 = lean_unsigned_to_nat(1u);
x_30 = l_Lean_Syntax_getArg(x_1, x_29);
x_31 = lean_ctor_get(x_27, 0);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_box(0);
x_33 = l_Lake_optsExt;
x_34 = lean_ctor_get_uint8(x_33, sizeof(void*)*3);
x_35 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_32, x_33, x_31, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_free_object(x_25);
x_36 = lean_mk_string_unchecked("dummyGetConfig\?", 15, 15);
x_37 = l_Lean_Name_mkStr3(x_12, x_13, x_36);
x_38 = lean_box(0);
x_39 = lean_unbox(x_38);
x_40 = l_Lean_mkCIdentFrom(x_1, x_37, x_39);
x_46 = l_Lean_Syntax_getId(x_30);
lean_dec(x_30);
x_47 = lean_box(0);
lean_inc(x_46);
x_48 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_47, x_46);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
x_49 = l_Lean_quoteNameMk(x_46);
x_41 = x_49;
goto block_45;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_46);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_mk_string_unchecked("Lean", 4, 4);
x_52 = lean_mk_string_unchecked("Parser", 6, 6);
x_53 = lean_mk_string_unchecked("Term", 4, 4);
x_54 = lean_mk_string_unchecked("quotedName", 10, 10);
x_55 = l_Lean_Name_mkStr4(x_51, x_52, x_53, x_54);
x_56 = lean_mk_string_unchecked("`", 1, 1);
x_57 = lean_mk_string_unchecked(".", 1, 1);
x_58 = l_String_intercalate(x_57, x_50);
lean_dec(x_57);
x_59 = lean_string_append(x_56, x_58);
lean_dec(x_58);
x_60 = lean_box(2);
x_61 = l_Lean_Syntax_mkNameLit(x_59, x_60);
x_62 = lean_mk_empty_array_with_capacity(x_29);
x_63 = lean_array_push(x_62, x_61);
x_64 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_64, 0, x_60);
lean_ctor_set(x_64, 1, x_55);
lean_ctor_set(x_64, 2, x_63);
x_41 = x_64;
goto block_45;
}
block_45:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_mk_empty_array_with_capacity(x_29);
x_43 = lean_array_push(x_42, x_41);
x_44 = l_Lean_Syntax_mkApp(x_40, x_43);
x_17 = x_44;
x_18 = x_28;
goto block_23;
}
}
else
{
uint8_t x_65; 
lean_dec(x_13);
lean_dec(x_12);
x_65 = !lean_is_exclusive(x_35);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_35, 0);
x_67 = l_Lean_Syntax_getId(x_30);
lean_dec(x_30);
x_68 = l_Lean_NameMap_find_x3f(lean_box(0), x_66, x_67);
lean_dec(x_67);
lean_dec(x_66);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_st_ref_get(x_8, x_28);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_71 = lean_ctor_get(x_69, 0);
x_72 = lean_ctor_get(x_69, 1);
x_73 = lean_ctor_get(x_7, 5);
lean_inc(x_73);
x_74 = lean_box(0);
x_75 = lean_unbox(x_74);
x_76 = l_Lean_SourceInfo_fromRef(x_73, x_75);
lean_dec(x_73);
x_77 = lean_ctor_get(x_7, 10);
lean_inc(x_77);
x_78 = lean_ctor_get(x_71, 0);
lean_inc(x_78);
lean_dec(x_71);
x_79 = l_Lean_Environment_mainModule(x_78);
lean_dec(x_78);
x_80 = lean_mk_string_unchecked("Lean", 4, 4);
x_81 = lean_mk_string_unchecked("Parser", 6, 6);
x_82 = lean_mk_string_unchecked("Term", 4, 4);
x_83 = lean_mk_string_unchecked("typeAscription", 14, 14);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
x_84 = l_Lean_Name_mkStr4(x_80, x_81, x_82, x_83);
x_85 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_76);
lean_ctor_set_tag(x_69, 2);
lean_ctor_set(x_69, 1, x_85);
lean_ctor_set(x_69, 0, x_76);
x_86 = lean_mk_string_unchecked("none", 4, 4);
lean_inc(x_86);
x_87 = l_String_toSubstring_x27(x_86);
lean_inc(x_86);
x_88 = l_Lean_Name_mkStr1(x_86);
lean_inc(x_77);
lean_inc(x_79);
x_89 = l_Lean_addMacroScope(x_79, x_88, x_77);
x_90 = lean_mk_string_unchecked("Option", 6, 6);
lean_inc(x_90);
x_91 = l_Lean_Name_mkStr2(x_90, x_86);
x_92 = lean_box(0);
lean_ctor_set_tag(x_25, 1);
lean_ctor_set(x_25, 1, x_92);
lean_ctor_set(x_25, 0, x_91);
x_93 = lean_box(0);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_25);
lean_ctor_set(x_94, 1, x_93);
lean_inc(x_76);
x_95 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_95, 0, x_76);
lean_ctor_set(x_95, 1, x_87);
lean_ctor_set(x_95, 2, x_89);
lean_ctor_set(x_95, 3, x_94);
x_96 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_76);
x_97 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_97, 0, x_76);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_mk_string_unchecked("null", 4, 4);
x_99 = l_Lean_Name_mkStr1(x_98);
x_100 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_80);
x_101 = l_Lean_Name_mkStr4(x_80, x_81, x_82, x_100);
lean_inc(x_90);
x_102 = l_String_toSubstring_x27(x_90);
lean_inc(x_90);
x_103 = l_Lean_Name_mkStr1(x_90);
lean_inc(x_77);
lean_inc(x_103);
lean_inc(x_79);
x_104 = l_Lean_addMacroScope(x_79, x_103, x_77);
lean_inc(x_103);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_92);
lean_ctor_set_tag(x_35, 0);
lean_ctor_set(x_35, 0, x_103);
x_106 = l_Lean_Name_mkStr2(x_80, x_90);
x_107 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_93);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_35);
lean_ctor_set(x_109, 1, x_108);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_105);
lean_ctor_set(x_110, 1, x_109);
lean_inc(x_76);
x_111 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_111, 0, x_76);
lean_ctor_set(x_111, 1, x_102);
lean_ctor_set(x_111, 2, x_104);
lean_ctor_set(x_111, 3, x_110);
x_112 = lean_mk_string_unchecked("String", 6, 6);
lean_inc(x_112);
x_113 = l_String_toSubstring_x27(x_112);
x_114 = l_Lean_Name_mkStr1(x_112);
lean_inc(x_114);
x_115 = l_Lean_addMacroScope(x_79, x_114, x_77);
lean_inc(x_114);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_92);
x_117 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_117, 0, x_114);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_93);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_118);
lean_inc(x_76);
x_120 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_120, 0, x_76);
lean_ctor_set(x_120, 1, x_113);
lean_ctor_set(x_120, 2, x_115);
lean_ctor_set(x_120, 3, x_119);
lean_inc(x_99);
lean_inc(x_76);
x_121 = l_Lean_Syntax_node1(x_76, x_99, x_120);
lean_inc(x_76);
x_122 = l_Lean_Syntax_node2(x_76, x_101, x_111, x_121);
lean_inc(x_76);
x_123 = l_Lean_Syntax_node1(x_76, x_99, x_122);
x_124 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_76);
x_125 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_125, 0, x_76);
lean_ctor_set(x_125, 1, x_124);
x_126 = l_Lean_Syntax_node5(x_76, x_84, x_69, x_95, x_97, x_123, x_125);
x_17 = x_126;
x_18 = x_72;
goto block_23;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_127 = lean_ctor_get(x_69, 0);
x_128 = lean_ctor_get(x_69, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_69);
x_129 = lean_ctor_get(x_7, 5);
lean_inc(x_129);
x_130 = lean_box(0);
x_131 = lean_unbox(x_130);
x_132 = l_Lean_SourceInfo_fromRef(x_129, x_131);
lean_dec(x_129);
x_133 = lean_ctor_get(x_7, 10);
lean_inc(x_133);
x_134 = lean_ctor_get(x_127, 0);
lean_inc(x_134);
lean_dec(x_127);
x_135 = l_Lean_Environment_mainModule(x_134);
lean_dec(x_134);
x_136 = lean_mk_string_unchecked("Lean", 4, 4);
x_137 = lean_mk_string_unchecked("Parser", 6, 6);
x_138 = lean_mk_string_unchecked("Term", 4, 4);
x_139 = lean_mk_string_unchecked("typeAscription", 14, 14);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
x_140 = l_Lean_Name_mkStr4(x_136, x_137, x_138, x_139);
x_141 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_132);
x_142 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_142, 0, x_132);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_mk_string_unchecked("none", 4, 4);
lean_inc(x_143);
x_144 = l_String_toSubstring_x27(x_143);
lean_inc(x_143);
x_145 = l_Lean_Name_mkStr1(x_143);
lean_inc(x_133);
lean_inc(x_135);
x_146 = l_Lean_addMacroScope(x_135, x_145, x_133);
x_147 = lean_mk_string_unchecked("Option", 6, 6);
lean_inc(x_147);
x_148 = l_Lean_Name_mkStr2(x_147, x_143);
x_149 = lean_box(0);
lean_ctor_set_tag(x_25, 1);
lean_ctor_set(x_25, 1, x_149);
lean_ctor_set(x_25, 0, x_148);
x_150 = lean_box(0);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_25);
lean_ctor_set(x_151, 1, x_150);
lean_inc(x_132);
x_152 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_152, 0, x_132);
lean_ctor_set(x_152, 1, x_144);
lean_ctor_set(x_152, 2, x_146);
lean_ctor_set(x_152, 3, x_151);
x_153 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_132);
x_154 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_154, 0, x_132);
lean_ctor_set(x_154, 1, x_153);
x_155 = lean_mk_string_unchecked("null", 4, 4);
x_156 = l_Lean_Name_mkStr1(x_155);
x_157 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_136);
x_158 = l_Lean_Name_mkStr4(x_136, x_137, x_138, x_157);
lean_inc(x_147);
x_159 = l_String_toSubstring_x27(x_147);
lean_inc(x_147);
x_160 = l_Lean_Name_mkStr1(x_147);
lean_inc(x_133);
lean_inc(x_160);
lean_inc(x_135);
x_161 = l_Lean_addMacroScope(x_135, x_160, x_133);
lean_inc(x_160);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_149);
lean_ctor_set_tag(x_35, 0);
lean_ctor_set(x_35, 0, x_160);
x_163 = l_Lean_Name_mkStr2(x_136, x_147);
x_164 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_164, 0, x_163);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_150);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_35);
lean_ctor_set(x_166, 1, x_165);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_162);
lean_ctor_set(x_167, 1, x_166);
lean_inc(x_132);
x_168 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_168, 0, x_132);
lean_ctor_set(x_168, 1, x_159);
lean_ctor_set(x_168, 2, x_161);
lean_ctor_set(x_168, 3, x_167);
x_169 = lean_mk_string_unchecked("String", 6, 6);
lean_inc(x_169);
x_170 = l_String_toSubstring_x27(x_169);
x_171 = l_Lean_Name_mkStr1(x_169);
lean_inc(x_171);
x_172 = l_Lean_addMacroScope(x_135, x_171, x_133);
lean_inc(x_171);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_149);
x_174 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_174, 0, x_171);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_150);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_175);
lean_inc(x_132);
x_177 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_177, 0, x_132);
lean_ctor_set(x_177, 1, x_170);
lean_ctor_set(x_177, 2, x_172);
lean_ctor_set(x_177, 3, x_176);
lean_inc(x_156);
lean_inc(x_132);
x_178 = l_Lean_Syntax_node1(x_132, x_156, x_177);
lean_inc(x_132);
x_179 = l_Lean_Syntax_node2(x_132, x_158, x_168, x_178);
lean_inc(x_132);
x_180 = l_Lean_Syntax_node1(x_132, x_156, x_179);
x_181 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_132);
x_182 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_182, 0, x_132);
lean_ctor_set(x_182, 1, x_181);
x_183 = l_Lean_Syntax_node5(x_132, x_140, x_142, x_152, x_154, x_180, x_182);
x_17 = x_183;
x_18 = x_128;
goto block_23;
}
}
else
{
lean_object* x_184; lean_object* x_185; uint8_t x_186; 
lean_free_object(x_35);
x_184 = lean_ctor_get(x_68, 0);
lean_inc(x_184);
lean_dec(x_68);
x_185 = lean_st_ref_get(x_8, x_28);
x_186 = !lean_is_exclusive(x_185);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_187 = lean_ctor_get(x_185, 0);
x_188 = lean_ctor_get(x_185, 1);
x_189 = lean_ctor_get(x_7, 5);
lean_inc(x_189);
x_190 = lean_box(0);
x_191 = lean_unbox(x_190);
x_192 = l_Lean_SourceInfo_fromRef(x_189, x_191);
lean_dec(x_189);
x_193 = lean_ctor_get(x_7, 10);
lean_inc(x_193);
x_194 = lean_ctor_get(x_187, 0);
lean_inc(x_194);
lean_dec(x_187);
x_195 = l_Lean_Environment_mainModule(x_194);
lean_dec(x_194);
x_196 = lean_mk_string_unchecked("Lean", 4, 4);
x_197 = lean_mk_string_unchecked("Parser", 6, 6);
x_198 = lean_mk_string_unchecked("Term", 4, 4);
x_199 = lean_mk_string_unchecked("app", 3, 3);
x_200 = l_Lean_Name_mkStr4(x_196, x_197, x_198, x_199);
x_201 = lean_mk_string_unchecked("some", 4, 4);
lean_inc(x_201);
x_202 = l_String_toSubstring_x27(x_201);
lean_inc(x_201);
x_203 = l_Lean_Name_mkStr1(x_201);
x_204 = l_Lean_addMacroScope(x_195, x_203, x_193);
x_205 = lean_mk_string_unchecked("Option", 6, 6);
x_206 = l_Lean_Name_mkStr2(x_205, x_201);
x_207 = lean_box(0);
lean_ctor_set_tag(x_185, 1);
lean_ctor_set(x_185, 1, x_207);
lean_ctor_set(x_185, 0, x_206);
x_208 = lean_box(0);
lean_ctor_set_tag(x_25, 1);
lean_ctor_set(x_25, 1, x_208);
lean_ctor_set(x_25, 0, x_185);
lean_inc(x_192);
x_209 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_209, 0, x_192);
lean_ctor_set(x_209, 1, x_202);
lean_ctor_set(x_209, 2, x_204);
lean_ctor_set(x_209, 3, x_25);
x_210 = lean_mk_string_unchecked("null", 4, 4);
x_211 = l_Lean_Name_mkStr1(x_210);
lean_inc(x_192);
x_212 = l_Lean_Syntax_mkStrLit(x_184, x_192);
lean_dec(x_184);
lean_inc(x_192);
x_213 = l_Lean_Syntax_node1(x_192, x_211, x_212);
x_214 = l_Lean_Syntax_node2(x_192, x_200, x_209, x_213);
x_17 = x_214;
x_18 = x_188;
goto block_23;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_215 = lean_ctor_get(x_185, 0);
x_216 = lean_ctor_get(x_185, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_185);
x_217 = lean_ctor_get(x_7, 5);
lean_inc(x_217);
x_218 = lean_box(0);
x_219 = lean_unbox(x_218);
x_220 = l_Lean_SourceInfo_fromRef(x_217, x_219);
lean_dec(x_217);
x_221 = lean_ctor_get(x_7, 10);
lean_inc(x_221);
x_222 = lean_ctor_get(x_215, 0);
lean_inc(x_222);
lean_dec(x_215);
x_223 = l_Lean_Environment_mainModule(x_222);
lean_dec(x_222);
x_224 = lean_mk_string_unchecked("Lean", 4, 4);
x_225 = lean_mk_string_unchecked("Parser", 6, 6);
x_226 = lean_mk_string_unchecked("Term", 4, 4);
x_227 = lean_mk_string_unchecked("app", 3, 3);
x_228 = l_Lean_Name_mkStr4(x_224, x_225, x_226, x_227);
x_229 = lean_mk_string_unchecked("some", 4, 4);
lean_inc(x_229);
x_230 = l_String_toSubstring_x27(x_229);
lean_inc(x_229);
x_231 = l_Lean_Name_mkStr1(x_229);
x_232 = l_Lean_addMacroScope(x_223, x_231, x_221);
x_233 = lean_mk_string_unchecked("Option", 6, 6);
x_234 = l_Lean_Name_mkStr2(x_233, x_229);
x_235 = lean_box(0);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
x_237 = lean_box(0);
lean_ctor_set_tag(x_25, 1);
lean_ctor_set(x_25, 1, x_237);
lean_ctor_set(x_25, 0, x_236);
lean_inc(x_220);
x_238 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_238, 0, x_220);
lean_ctor_set(x_238, 1, x_230);
lean_ctor_set(x_238, 2, x_232);
lean_ctor_set(x_238, 3, x_25);
x_239 = lean_mk_string_unchecked("null", 4, 4);
x_240 = l_Lean_Name_mkStr1(x_239);
lean_inc(x_220);
x_241 = l_Lean_Syntax_mkStrLit(x_184, x_220);
lean_dec(x_184);
lean_inc(x_220);
x_242 = l_Lean_Syntax_node1(x_220, x_240, x_241);
x_243 = l_Lean_Syntax_node2(x_220, x_228, x_238, x_242);
x_17 = x_243;
x_18 = x_216;
goto block_23;
}
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_35, 0);
lean_inc(x_244);
lean_dec(x_35);
x_245 = l_Lean_Syntax_getId(x_30);
lean_dec(x_30);
x_246 = l_Lean_NameMap_find_x3f(lean_box(0), x_244, x_245);
lean_dec(x_245);
lean_dec(x_244);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_247 = lean_st_ref_get(x_8, x_28);
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_250 = x_247;
} else {
 lean_dec_ref(x_247);
 x_250 = lean_box(0);
}
x_251 = lean_ctor_get(x_7, 5);
lean_inc(x_251);
x_252 = lean_box(0);
x_253 = lean_unbox(x_252);
x_254 = l_Lean_SourceInfo_fromRef(x_251, x_253);
lean_dec(x_251);
x_255 = lean_ctor_get(x_7, 10);
lean_inc(x_255);
x_256 = lean_ctor_get(x_248, 0);
lean_inc(x_256);
lean_dec(x_248);
x_257 = l_Lean_Environment_mainModule(x_256);
lean_dec(x_256);
x_258 = lean_mk_string_unchecked("Lean", 4, 4);
x_259 = lean_mk_string_unchecked("Parser", 6, 6);
x_260 = lean_mk_string_unchecked("Term", 4, 4);
x_261 = lean_mk_string_unchecked("typeAscription", 14, 14);
lean_inc(x_260);
lean_inc(x_259);
lean_inc(x_258);
x_262 = l_Lean_Name_mkStr4(x_258, x_259, x_260, x_261);
x_263 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_254);
if (lean_is_scalar(x_250)) {
 x_264 = lean_alloc_ctor(2, 2, 0);
} else {
 x_264 = x_250;
 lean_ctor_set_tag(x_264, 2);
}
lean_ctor_set(x_264, 0, x_254);
lean_ctor_set(x_264, 1, x_263);
x_265 = lean_mk_string_unchecked("none", 4, 4);
lean_inc(x_265);
x_266 = l_String_toSubstring_x27(x_265);
lean_inc(x_265);
x_267 = l_Lean_Name_mkStr1(x_265);
lean_inc(x_255);
lean_inc(x_257);
x_268 = l_Lean_addMacroScope(x_257, x_267, x_255);
x_269 = lean_mk_string_unchecked("Option", 6, 6);
lean_inc(x_269);
x_270 = l_Lean_Name_mkStr2(x_269, x_265);
x_271 = lean_box(0);
lean_ctor_set_tag(x_25, 1);
lean_ctor_set(x_25, 1, x_271);
lean_ctor_set(x_25, 0, x_270);
x_272 = lean_box(0);
x_273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_273, 0, x_25);
lean_ctor_set(x_273, 1, x_272);
lean_inc(x_254);
x_274 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_274, 0, x_254);
lean_ctor_set(x_274, 1, x_266);
lean_ctor_set(x_274, 2, x_268);
lean_ctor_set(x_274, 3, x_273);
x_275 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_254);
x_276 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_276, 0, x_254);
lean_ctor_set(x_276, 1, x_275);
x_277 = lean_mk_string_unchecked("null", 4, 4);
x_278 = l_Lean_Name_mkStr1(x_277);
x_279 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_258);
x_280 = l_Lean_Name_mkStr4(x_258, x_259, x_260, x_279);
lean_inc(x_269);
x_281 = l_String_toSubstring_x27(x_269);
lean_inc(x_269);
x_282 = l_Lean_Name_mkStr1(x_269);
lean_inc(x_255);
lean_inc(x_282);
lean_inc(x_257);
x_283 = l_Lean_addMacroScope(x_257, x_282, x_255);
lean_inc(x_282);
x_284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_271);
x_285 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_285, 0, x_282);
x_286 = l_Lean_Name_mkStr2(x_258, x_269);
x_287 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_287, 0, x_286);
x_288 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_272);
x_289 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_289, 0, x_285);
lean_ctor_set(x_289, 1, x_288);
x_290 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_290, 0, x_284);
lean_ctor_set(x_290, 1, x_289);
lean_inc(x_254);
x_291 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_291, 0, x_254);
lean_ctor_set(x_291, 1, x_281);
lean_ctor_set(x_291, 2, x_283);
lean_ctor_set(x_291, 3, x_290);
x_292 = lean_mk_string_unchecked("String", 6, 6);
lean_inc(x_292);
x_293 = l_String_toSubstring_x27(x_292);
x_294 = l_Lean_Name_mkStr1(x_292);
lean_inc(x_294);
x_295 = l_Lean_addMacroScope(x_257, x_294, x_255);
lean_inc(x_294);
x_296 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_296, 0, x_294);
lean_ctor_set(x_296, 1, x_271);
x_297 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_297, 0, x_294);
x_298 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_298, 1, x_272);
x_299 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_299, 0, x_296);
lean_ctor_set(x_299, 1, x_298);
lean_inc(x_254);
x_300 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_300, 0, x_254);
lean_ctor_set(x_300, 1, x_293);
lean_ctor_set(x_300, 2, x_295);
lean_ctor_set(x_300, 3, x_299);
lean_inc(x_278);
lean_inc(x_254);
x_301 = l_Lean_Syntax_node1(x_254, x_278, x_300);
lean_inc(x_254);
x_302 = l_Lean_Syntax_node2(x_254, x_280, x_291, x_301);
lean_inc(x_254);
x_303 = l_Lean_Syntax_node1(x_254, x_278, x_302);
x_304 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_254);
x_305 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_305, 0, x_254);
lean_ctor_set(x_305, 1, x_304);
x_306 = l_Lean_Syntax_node5(x_254, x_262, x_264, x_274, x_276, x_303, x_305);
x_17 = x_306;
x_18 = x_249;
goto block_23;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; uint8_t x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_307 = lean_ctor_get(x_246, 0);
lean_inc(x_307);
lean_dec(x_246);
x_308 = lean_st_ref_get(x_8, x_28);
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_308, 1);
lean_inc(x_310);
if (lean_is_exclusive(x_308)) {
 lean_ctor_release(x_308, 0);
 lean_ctor_release(x_308, 1);
 x_311 = x_308;
} else {
 lean_dec_ref(x_308);
 x_311 = lean_box(0);
}
x_312 = lean_ctor_get(x_7, 5);
lean_inc(x_312);
x_313 = lean_box(0);
x_314 = lean_unbox(x_313);
x_315 = l_Lean_SourceInfo_fromRef(x_312, x_314);
lean_dec(x_312);
x_316 = lean_ctor_get(x_7, 10);
lean_inc(x_316);
x_317 = lean_ctor_get(x_309, 0);
lean_inc(x_317);
lean_dec(x_309);
x_318 = l_Lean_Environment_mainModule(x_317);
lean_dec(x_317);
x_319 = lean_mk_string_unchecked("Lean", 4, 4);
x_320 = lean_mk_string_unchecked("Parser", 6, 6);
x_321 = lean_mk_string_unchecked("Term", 4, 4);
x_322 = lean_mk_string_unchecked("app", 3, 3);
x_323 = l_Lean_Name_mkStr4(x_319, x_320, x_321, x_322);
x_324 = lean_mk_string_unchecked("some", 4, 4);
lean_inc(x_324);
x_325 = l_String_toSubstring_x27(x_324);
lean_inc(x_324);
x_326 = l_Lean_Name_mkStr1(x_324);
x_327 = l_Lean_addMacroScope(x_318, x_326, x_316);
x_328 = lean_mk_string_unchecked("Option", 6, 6);
x_329 = l_Lean_Name_mkStr2(x_328, x_324);
x_330 = lean_box(0);
if (lean_is_scalar(x_311)) {
 x_331 = lean_alloc_ctor(1, 2, 0);
} else {
 x_331 = x_311;
 lean_ctor_set_tag(x_331, 1);
}
lean_ctor_set(x_331, 0, x_329);
lean_ctor_set(x_331, 1, x_330);
x_332 = lean_box(0);
lean_ctor_set_tag(x_25, 1);
lean_ctor_set(x_25, 1, x_332);
lean_ctor_set(x_25, 0, x_331);
lean_inc(x_315);
x_333 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_333, 0, x_315);
lean_ctor_set(x_333, 1, x_325);
lean_ctor_set(x_333, 2, x_327);
lean_ctor_set(x_333, 3, x_25);
x_334 = lean_mk_string_unchecked("null", 4, 4);
x_335 = l_Lean_Name_mkStr1(x_334);
lean_inc(x_315);
x_336 = l_Lean_Syntax_mkStrLit(x_307, x_315);
lean_dec(x_307);
lean_inc(x_315);
x_337 = l_Lean_Syntax_node1(x_315, x_335, x_336);
x_338 = l_Lean_Syntax_node2(x_315, x_323, x_333, x_337);
x_17 = x_338;
x_18 = x_310;
goto block_23;
}
}
}
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; lean_object* x_347; 
x_339 = lean_ctor_get(x_25, 0);
x_340 = lean_ctor_get(x_25, 1);
lean_inc(x_340);
lean_inc(x_339);
lean_dec(x_25);
x_341 = lean_unsigned_to_nat(1u);
x_342 = l_Lean_Syntax_getArg(x_1, x_341);
x_343 = lean_ctor_get(x_339, 0);
lean_inc(x_343);
lean_dec(x_339);
x_344 = lean_box(0);
x_345 = l_Lake_optsExt;
x_346 = lean_ctor_get_uint8(x_345, sizeof(void*)*3);
x_347 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_344, x_345, x_343, x_346);
if (lean_obj_tag(x_347) == 0)
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; uint8_t x_351; lean_object* x_352; lean_object* x_353; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_348 = lean_mk_string_unchecked("dummyGetConfig\?", 15, 15);
x_349 = l_Lean_Name_mkStr3(x_12, x_13, x_348);
x_350 = lean_box(0);
x_351 = lean_unbox(x_350);
x_352 = l_Lean_mkCIdentFrom(x_1, x_349, x_351);
x_358 = l_Lean_Syntax_getId(x_342);
lean_dec(x_342);
x_359 = lean_box(0);
lean_inc(x_358);
x_360 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_359, x_358);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_361; 
x_361 = l_Lean_quoteNameMk(x_358);
x_353 = x_361;
goto block_357;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
lean_dec(x_358);
x_362 = lean_ctor_get(x_360, 0);
lean_inc(x_362);
lean_dec(x_360);
x_363 = lean_mk_string_unchecked("Lean", 4, 4);
x_364 = lean_mk_string_unchecked("Parser", 6, 6);
x_365 = lean_mk_string_unchecked("Term", 4, 4);
x_366 = lean_mk_string_unchecked("quotedName", 10, 10);
x_367 = l_Lean_Name_mkStr4(x_363, x_364, x_365, x_366);
x_368 = lean_mk_string_unchecked("`", 1, 1);
x_369 = lean_mk_string_unchecked(".", 1, 1);
x_370 = l_String_intercalate(x_369, x_362);
lean_dec(x_369);
x_371 = lean_string_append(x_368, x_370);
lean_dec(x_370);
x_372 = lean_box(2);
x_373 = l_Lean_Syntax_mkNameLit(x_371, x_372);
x_374 = lean_mk_empty_array_with_capacity(x_341);
x_375 = lean_array_push(x_374, x_373);
x_376 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_376, 0, x_372);
lean_ctor_set(x_376, 1, x_367);
lean_ctor_set(x_376, 2, x_375);
x_353 = x_376;
goto block_357;
}
block_357:
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_354 = lean_mk_empty_array_with_capacity(x_341);
x_355 = lean_array_push(x_354, x_353);
x_356 = l_Lean_Syntax_mkApp(x_352, x_355);
x_17 = x_356;
x_18 = x_340;
goto block_23;
}
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
lean_dec(x_13);
lean_dec(x_12);
x_377 = lean_ctor_get(x_347, 0);
lean_inc(x_377);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 x_378 = x_347;
} else {
 lean_dec_ref(x_347);
 x_378 = lean_box(0);
}
x_379 = l_Lean_Syntax_getId(x_342);
lean_dec(x_342);
x_380 = l_Lean_NameMap_find_x3f(lean_box(0), x_377, x_379);
lean_dec(x_379);
lean_dec(x_377);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_381 = lean_st_ref_get(x_8, x_340);
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_381, 1);
lean_inc(x_383);
if (lean_is_exclusive(x_381)) {
 lean_ctor_release(x_381, 0);
 lean_ctor_release(x_381, 1);
 x_384 = x_381;
} else {
 lean_dec_ref(x_381);
 x_384 = lean_box(0);
}
x_385 = lean_ctor_get(x_7, 5);
lean_inc(x_385);
x_386 = lean_box(0);
x_387 = lean_unbox(x_386);
x_388 = l_Lean_SourceInfo_fromRef(x_385, x_387);
lean_dec(x_385);
x_389 = lean_ctor_get(x_7, 10);
lean_inc(x_389);
x_390 = lean_ctor_get(x_382, 0);
lean_inc(x_390);
lean_dec(x_382);
x_391 = l_Lean_Environment_mainModule(x_390);
lean_dec(x_390);
x_392 = lean_mk_string_unchecked("Lean", 4, 4);
x_393 = lean_mk_string_unchecked("Parser", 6, 6);
x_394 = lean_mk_string_unchecked("Term", 4, 4);
x_395 = lean_mk_string_unchecked("typeAscription", 14, 14);
lean_inc(x_394);
lean_inc(x_393);
lean_inc(x_392);
x_396 = l_Lean_Name_mkStr4(x_392, x_393, x_394, x_395);
x_397 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_388);
if (lean_is_scalar(x_384)) {
 x_398 = lean_alloc_ctor(2, 2, 0);
} else {
 x_398 = x_384;
 lean_ctor_set_tag(x_398, 2);
}
lean_ctor_set(x_398, 0, x_388);
lean_ctor_set(x_398, 1, x_397);
x_399 = lean_mk_string_unchecked("none", 4, 4);
lean_inc(x_399);
x_400 = l_String_toSubstring_x27(x_399);
lean_inc(x_399);
x_401 = l_Lean_Name_mkStr1(x_399);
lean_inc(x_389);
lean_inc(x_391);
x_402 = l_Lean_addMacroScope(x_391, x_401, x_389);
x_403 = lean_mk_string_unchecked("Option", 6, 6);
lean_inc(x_403);
x_404 = l_Lean_Name_mkStr2(x_403, x_399);
x_405 = lean_box(0);
x_406 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_406, 0, x_404);
lean_ctor_set(x_406, 1, x_405);
x_407 = lean_box(0);
x_408 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_408, 0, x_406);
lean_ctor_set(x_408, 1, x_407);
lean_inc(x_388);
x_409 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_409, 0, x_388);
lean_ctor_set(x_409, 1, x_400);
lean_ctor_set(x_409, 2, x_402);
lean_ctor_set(x_409, 3, x_408);
x_410 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_388);
x_411 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_411, 0, x_388);
lean_ctor_set(x_411, 1, x_410);
x_412 = lean_mk_string_unchecked("null", 4, 4);
x_413 = l_Lean_Name_mkStr1(x_412);
x_414 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_392);
x_415 = l_Lean_Name_mkStr4(x_392, x_393, x_394, x_414);
lean_inc(x_403);
x_416 = l_String_toSubstring_x27(x_403);
lean_inc(x_403);
x_417 = l_Lean_Name_mkStr1(x_403);
lean_inc(x_389);
lean_inc(x_417);
lean_inc(x_391);
x_418 = l_Lean_addMacroScope(x_391, x_417, x_389);
lean_inc(x_417);
x_419 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_419, 0, x_417);
lean_ctor_set(x_419, 1, x_405);
if (lean_is_scalar(x_378)) {
 x_420 = lean_alloc_ctor(0, 1, 0);
} else {
 x_420 = x_378;
 lean_ctor_set_tag(x_420, 0);
}
lean_ctor_set(x_420, 0, x_417);
x_421 = l_Lean_Name_mkStr2(x_392, x_403);
x_422 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_422, 0, x_421);
x_423 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_423, 0, x_422);
lean_ctor_set(x_423, 1, x_407);
x_424 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_424, 0, x_420);
lean_ctor_set(x_424, 1, x_423);
x_425 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_425, 0, x_419);
lean_ctor_set(x_425, 1, x_424);
lean_inc(x_388);
x_426 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_426, 0, x_388);
lean_ctor_set(x_426, 1, x_416);
lean_ctor_set(x_426, 2, x_418);
lean_ctor_set(x_426, 3, x_425);
x_427 = lean_mk_string_unchecked("String", 6, 6);
lean_inc(x_427);
x_428 = l_String_toSubstring_x27(x_427);
x_429 = l_Lean_Name_mkStr1(x_427);
lean_inc(x_429);
x_430 = l_Lean_addMacroScope(x_391, x_429, x_389);
lean_inc(x_429);
x_431 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_431, 0, x_429);
lean_ctor_set(x_431, 1, x_405);
x_432 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_432, 0, x_429);
x_433 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_433, 0, x_432);
lean_ctor_set(x_433, 1, x_407);
x_434 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_434, 0, x_431);
lean_ctor_set(x_434, 1, x_433);
lean_inc(x_388);
x_435 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_435, 0, x_388);
lean_ctor_set(x_435, 1, x_428);
lean_ctor_set(x_435, 2, x_430);
lean_ctor_set(x_435, 3, x_434);
lean_inc(x_413);
lean_inc(x_388);
x_436 = l_Lean_Syntax_node1(x_388, x_413, x_435);
lean_inc(x_388);
x_437 = l_Lean_Syntax_node2(x_388, x_415, x_426, x_436);
lean_inc(x_388);
x_438 = l_Lean_Syntax_node1(x_388, x_413, x_437);
x_439 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_388);
x_440 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_440, 0, x_388);
lean_ctor_set(x_440, 1, x_439);
x_441 = l_Lean_Syntax_node5(x_388, x_396, x_398, x_409, x_411, x_438, x_440);
x_17 = x_441;
x_18 = x_383;
goto block_23;
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; uint8_t x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
lean_dec(x_378);
x_442 = lean_ctor_get(x_380, 0);
lean_inc(x_442);
lean_dec(x_380);
x_443 = lean_st_ref_get(x_8, x_340);
x_444 = lean_ctor_get(x_443, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_443, 1);
lean_inc(x_445);
if (lean_is_exclusive(x_443)) {
 lean_ctor_release(x_443, 0);
 lean_ctor_release(x_443, 1);
 x_446 = x_443;
} else {
 lean_dec_ref(x_443);
 x_446 = lean_box(0);
}
x_447 = lean_ctor_get(x_7, 5);
lean_inc(x_447);
x_448 = lean_box(0);
x_449 = lean_unbox(x_448);
x_450 = l_Lean_SourceInfo_fromRef(x_447, x_449);
lean_dec(x_447);
x_451 = lean_ctor_get(x_7, 10);
lean_inc(x_451);
x_452 = lean_ctor_get(x_444, 0);
lean_inc(x_452);
lean_dec(x_444);
x_453 = l_Lean_Environment_mainModule(x_452);
lean_dec(x_452);
x_454 = lean_mk_string_unchecked("Lean", 4, 4);
x_455 = lean_mk_string_unchecked("Parser", 6, 6);
x_456 = lean_mk_string_unchecked("Term", 4, 4);
x_457 = lean_mk_string_unchecked("app", 3, 3);
x_458 = l_Lean_Name_mkStr4(x_454, x_455, x_456, x_457);
x_459 = lean_mk_string_unchecked("some", 4, 4);
lean_inc(x_459);
x_460 = l_String_toSubstring_x27(x_459);
lean_inc(x_459);
x_461 = l_Lean_Name_mkStr1(x_459);
x_462 = l_Lean_addMacroScope(x_453, x_461, x_451);
x_463 = lean_mk_string_unchecked("Option", 6, 6);
x_464 = l_Lean_Name_mkStr2(x_463, x_459);
x_465 = lean_box(0);
if (lean_is_scalar(x_446)) {
 x_466 = lean_alloc_ctor(1, 2, 0);
} else {
 x_466 = x_446;
 lean_ctor_set_tag(x_466, 1);
}
lean_ctor_set(x_466, 0, x_464);
lean_ctor_set(x_466, 1, x_465);
x_467 = lean_box(0);
x_468 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_468, 0, x_466);
lean_ctor_set(x_468, 1, x_467);
lean_inc(x_450);
x_469 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_469, 0, x_450);
lean_ctor_set(x_469, 1, x_460);
lean_ctor_set(x_469, 2, x_462);
lean_ctor_set(x_469, 3, x_468);
x_470 = lean_mk_string_unchecked("null", 4, 4);
x_471 = l_Lean_Name_mkStr1(x_470);
lean_inc(x_450);
x_472 = l_Lean_Syntax_mkStrLit(x_442, x_450);
lean_dec(x_442);
lean_inc(x_450);
x_473 = l_Lean_Syntax_node1(x_450, x_471, x_472);
x_474 = l_Lean_Syntax_node2(x_450, x_458, x_469, x_473);
x_17 = x_474;
x_18 = x_445;
goto block_23;
}
}
}
}
block_23:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_box(x_16);
x_20 = lean_box(x_16);
lean_inc(x_17);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(x_21, 0, x_17);
lean_closure_set(x_21, 1, x_2);
lean_closure_set(x_21, 2, x_19);
lean_closure_set(x_21, 3, x_20);
x_22 = l_Lean_Elab_Term_withMacroExpansion___redArg(x_1, x_17, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
return x_22;
}
}
else
{
uint8_t x_475; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_475 = !lean_is_exclusive(x_10);
if (x_475 == 0)
{
return x_10;
}
else
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_476 = lean_ctor_get(x_10, 0);
x_477 = lean_ctor_get(x_10, 1);
lean_inc(x_477);
lean_inc(x_476);
lean_dec(x_10);
x_478 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_478, 0, x_476);
lean_ctor_set(x_478, 1, x_477);
return x_478;
}
}
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lake_DSL_elabGetConfig__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = lean_mk_string_unchecked("Lake", 4, 4);
x_4 = lean_mk_string_unchecked("DSL", 3, 3);
x_5 = lean_mk_string_unchecked("getConfig", 9, 9);
lean_inc(x_4);
lean_inc(x_3);
x_6 = l_Lean_Name_mkStr3(x_3, x_4, x_5);
x_7 = lean_mk_string_unchecked("elabGetConfig", 13, 13);
x_8 = l_Lean_Name_mkStr3(x_3, x_4, x_7);
x_9 = lean_alloc_closure((void*)(l_Lake_DSL_elabGetConfig), 9, 0);
x_10 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_6, x_8, x_9, x_1);
return x_10;
}
}
lean_object* initialize_Lean_Elab_ElabRules(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_DSL_Extensions(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_DSL_Syntax(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_DSL_Config(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_ElabRules(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_DSL_Extensions(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_DSL_Syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_DSL_dummyDir = _init_l_Lake_DSL_dummyDir();
lean_mark_persistent(l_Lake_DSL_dummyDir);
if (builtin) {res = l___regBuiltin_Lake_DSL_elabDirConst__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lake_DSL_elabGetConfig__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
