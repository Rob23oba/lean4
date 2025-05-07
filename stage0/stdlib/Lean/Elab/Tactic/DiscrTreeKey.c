// Lean compiler output
// Module: Lean.Elab.Tactic.DiscrTreeKey
// Imports: Init.Tactics Lean.Elab.Command Lean.Meta.Tactic.Simp.SimpTheorems
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
LEAN_EXPORT lean_object* l_Lean_logInfo___at___Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_keysAsPattern(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___lam__0(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_log___at___Lean_logError___at___Lean_Elab_logException___at___Lean_Elab_withLogging___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore_spec__2_spec__2_spec__2_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_____private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_mkPath(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
extern lean_object* l_Lean_Meta_simpGlobalConfig;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_____private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1(lean_object*);
lean_object* l_Lean_Meta_whnfR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; uint8_t x_30; uint64_t x_31; lean_object* x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint8_t x_36; uint64_t x_37; uint64_t x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_8 = lean_box(0);
x_9 = lean_box(0);
x_10 = lean_box(2);
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get_uint8(x_11, 0);
x_13 = lean_ctor_get_uint8(x_11, 1);
x_14 = lean_ctor_get_uint8(x_11, 2);
x_15 = lean_ctor_get_uint8(x_11, 3);
x_16 = lean_ctor_get_uint8(x_11, 4);
x_17 = lean_ctor_get_uint8(x_11, 5);
x_18 = lean_ctor_get_uint8(x_11, 6);
x_19 = lean_ctor_get_uint8(x_11, 7);
x_20 = lean_ctor_get_uint8(x_11, 8);
x_21 = lean_ctor_get_uint8(x_11, 10);
x_22 = lean_ctor_get_uint8(x_11, 11);
x_23 = lean_ctor_get_uint8(x_11, 12);
x_24 = lean_ctor_get_uint8(x_11, 13);
x_25 = lean_ctor_get_uint8(x_11, 14);
x_26 = lean_ctor_get_uint8(x_11, 15);
x_27 = lean_ctor_get_uint8(x_11, 16);
x_28 = lean_ctor_get_uint8(x_11, 17);
x_29 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_29, 0, x_12);
lean_ctor_set_uint8(x_29, 1, x_13);
lean_ctor_set_uint8(x_29, 2, x_14);
lean_ctor_set_uint8(x_29, 3, x_15);
lean_ctor_set_uint8(x_29, 4, x_16);
lean_ctor_set_uint8(x_29, 5, x_17);
lean_ctor_set_uint8(x_29, 6, x_18);
lean_ctor_set_uint8(x_29, 7, x_19);
lean_ctor_set_uint8(x_29, 8, x_20);
x_30 = lean_unbox(x_10);
lean_ctor_set_uint8(x_29, 9, x_30);
lean_ctor_set_uint8(x_29, 10, x_21);
lean_ctor_set_uint8(x_29, 11, x_22);
lean_ctor_set_uint8(x_29, 12, x_23);
lean_ctor_set_uint8(x_29, 13, x_24);
lean_ctor_set_uint8(x_29, 14, x_25);
lean_ctor_set_uint8(x_29, 15, x_26);
lean_ctor_set_uint8(x_29, 16, x_27);
lean_ctor_set_uint8(x_29, 17, x_28);
x_31 = lean_ctor_get_uint64(x_3, sizeof(void*)*7);
x_32 = lean_unsigned_to_nat(2u);
x_33 = lean_uint64_of_nat(x_32);
x_34 = lean_uint64_shift_right(x_31, x_33);
x_35 = lean_uint64_shift_left(x_34, x_33);
x_36 = lean_unbox(x_10);
x_37 = l_Lean_Meta_TransparencyMode_toUInt64(x_36);
x_38 = lean_uint64_lor(x_35, x_37);
x_39 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 8);
x_40 = lean_ctor_get(x_3, 1);
x_41 = lean_ctor_get(x_3, 2);
x_42 = lean_ctor_get(x_3, 3);
x_43 = lean_ctor_get(x_3, 4);
x_44 = lean_ctor_get(x_3, 5);
x_45 = lean_ctor_get(x_3, 6);
x_46 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 9);
x_47 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 10);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
x_48 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_48, 0, x_29);
lean_ctor_set(x_48, 1, x_40);
lean_ctor_set(x_48, 2, x_41);
lean_ctor_set(x_48, 3, x_42);
lean_ctor_set(x_48, 4, x_43);
lean_ctor_set(x_48, 5, x_44);
lean_ctor_set(x_48, 6, x_45);
lean_ctor_set_uint64(x_48, sizeof(void*)*7, x_38);
lean_ctor_set_uint8(x_48, sizeof(void*)*7 + 8, x_39);
lean_ctor_set_uint8(x_48, sizeof(void*)*7 + 9, x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*7 + 10, x_47);
x_49 = lean_unbox(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_50 = l_Lean_Meta_forallMetaTelescopeReducing(x_1, x_8, x_49, x_48, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_ctor_get(x_51, 1);
x_54 = lean_ctor_get(x_51, 0);
lean_dec(x_54);
x_55 = lean_ctor_get(x_50, 1);
lean_inc(x_55);
lean_dec(x_50);
x_56 = !lean_is_exclusive(x_53);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_53, 1);
x_58 = lean_ctor_get(x_53, 0);
lean_dec(x_58);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_59 = l_Lean_Meta_whnfR(x_57, x_3, x_4, x_5, x_6, x_55);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
if (x_2 == 0)
{
lean_object* x_104; 
lean_free_object(x_53);
lean_free_object(x_51);
x_104 = l_Lean_Meta_DiscrTree_mkPath(x_60, x_2, x_3, x_4, x_5, x_6, x_61);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_105 = lean_mk_string_unchecked("Eq", 2, 2);
x_106 = l_Lean_Name_mkStr1(x_105);
x_107 = lean_unsigned_to_nat(3u);
x_108 = l_Lean_Expr_isAppOfArity(x_60, x_106, x_107);
lean_dec(x_106);
if (x_108 == 0)
{
lean_object* x_109; 
lean_free_object(x_53);
lean_free_object(x_51);
x_109 = lean_box(0);
x_62 = x_109;
goto block_103;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_110 = l_Lean_Expr_appFn_x21(x_60);
x_111 = l_Lean_Expr_appFn_x21(x_110);
x_112 = l_Lean_Expr_appArg_x21(x_111);
lean_dec(x_111);
x_113 = l_Lean_Expr_appArg_x21(x_110);
lean_dec(x_110);
x_114 = l_Lean_Expr_appArg_x21(x_60);
lean_ctor_set(x_53, 1, x_114);
lean_ctor_set(x_53, 0, x_113);
lean_ctor_set(x_51, 0, x_112);
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_51);
x_62 = x_115;
goto block_103;
}
}
block_103:
{
lean_object* x_63; lean_object* x_64; uint64_t x_65; lean_object* x_66; 
x_63 = l_Lean_Meta_simpGlobalConfig;
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get_uint64(x_63, sizeof(void*)*1);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
x_66 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_40);
lean_ctor_set(x_66, 2, x_41);
lean_ctor_set(x_66, 3, x_42);
lean_ctor_set(x_66, 4, x_43);
lean_ctor_set(x_66, 5, x_44);
lean_ctor_set(x_66, 6, x_45);
lean_ctor_set_uint64(x_66, sizeof(void*)*7, x_65);
lean_ctor_set_uint8(x_66, sizeof(void*)*7 + 8, x_39);
lean_ctor_set_uint8(x_66, sizeof(void*)*7 + 9, x_46);
lean_ctor_set_uint8(x_66, sizeof(void*)*7 + 10, x_47);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_mk_string_unchecked("Iff", 3, 3);
x_68 = l_Lean_Name_mkStr1(x_67);
x_69 = l_Lean_Expr_isAppOfArity(x_60, x_68, x_32);
lean_dec(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_70 = lean_mk_string_unchecked("Ne", 2, 2);
x_71 = l_Lean_Name_mkStr1(x_70);
x_72 = lean_unsigned_to_nat(3u);
x_73 = l_Lean_Expr_isAppOfArity(x_60, x_71, x_72);
lean_dec(x_71);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_74 = lean_mk_string_unchecked("Not", 3, 3);
x_75 = l_Lean_Name_mkStr1(x_74);
x_76 = lean_unsigned_to_nat(1u);
x_77 = l_Lean_Expr_isAppOfArity(x_60, x_75, x_76);
lean_dec(x_75);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = l_Lean_Meta_DiscrTree_mkPath(x_60, x_77, x_66, x_4, x_5, x_6, x_61);
lean_dec(x_66);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = l_Lean_Expr_appArg_x21(x_60);
lean_dec(x_60);
x_80 = l_Lean_Meta_DiscrTree_mkPath(x_79, x_73, x_66, x_4, x_5, x_6, x_61);
lean_dec(x_66);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = l_Lean_Expr_appFn_x21(x_60);
x_82 = l_Lean_Expr_appArg_x21(x_81);
lean_dec(x_81);
x_83 = l_Lean_Expr_appArg_x21(x_60);
lean_dec(x_60);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_66);
x_84 = l_Lean_Meta_mkEq(x_82, x_83, x_66, x_4, x_5, x_6, x_61);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_Lean_Meta_DiscrTree_mkPath(x_85, x_69, x_66, x_4, x_5, x_6, x_86);
lean_dec(x_66);
return x_87;
}
else
{
uint8_t x_88; 
lean_dec(x_66);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_88 = !lean_is_exclusive(x_84);
if (x_88 == 0)
{
return x_84;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_84, 0);
x_90 = lean_ctor_get(x_84, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_84);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; 
x_92 = l_Lean_Expr_appFn_x21(x_60);
lean_dec(x_60);
x_93 = l_Lean_Expr_appArg_x21(x_92);
lean_dec(x_92);
x_94 = lean_box(0);
x_95 = lean_unbox(x_94);
x_96 = l_Lean_Meta_DiscrTree_mkPath(x_93, x_95, x_66, x_4, x_5, x_6, x_61);
lean_dec(x_66);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; 
lean_dec(x_60);
x_97 = lean_ctor_get(x_62, 0);
lean_inc(x_97);
lean_dec(x_62);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_dec(x_98);
x_100 = lean_box(0);
x_101 = lean_unbox(x_100);
x_102 = l_Lean_Meta_DiscrTree_mkPath(x_99, x_101, x_66, x_4, x_5, x_6, x_61);
lean_dec(x_66);
return x_102;
}
}
}
else
{
uint8_t x_116; 
lean_free_object(x_53);
lean_free_object(x_51);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_116 = !lean_is_exclusive(x_59);
if (x_116 == 0)
{
return x_59;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_59, 0);
x_118 = lean_ctor_get(x_59, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_59);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_53, 1);
lean_inc(x_120);
lean_dec(x_53);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_121 = l_Lean_Meta_whnfR(x_120, x_3, x_4, x_5, x_6, x_55);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
if (x_2 == 0)
{
lean_object* x_166; 
lean_free_object(x_51);
x_166 = l_Lean_Meta_DiscrTree_mkPath(x_122, x_2, x_3, x_4, x_5, x_6, x_123);
return x_166;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_167 = lean_mk_string_unchecked("Eq", 2, 2);
x_168 = l_Lean_Name_mkStr1(x_167);
x_169 = lean_unsigned_to_nat(3u);
x_170 = l_Lean_Expr_isAppOfArity(x_122, x_168, x_169);
lean_dec(x_168);
if (x_170 == 0)
{
lean_object* x_171; 
lean_free_object(x_51);
x_171 = lean_box(0);
x_124 = x_171;
goto block_165;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_172 = l_Lean_Expr_appFn_x21(x_122);
x_173 = l_Lean_Expr_appFn_x21(x_172);
x_174 = l_Lean_Expr_appArg_x21(x_173);
lean_dec(x_173);
x_175 = l_Lean_Expr_appArg_x21(x_172);
lean_dec(x_172);
x_176 = l_Lean_Expr_appArg_x21(x_122);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
lean_ctor_set(x_51, 1, x_177);
lean_ctor_set(x_51, 0, x_174);
x_178 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_178, 0, x_51);
x_124 = x_178;
goto block_165;
}
}
block_165:
{
lean_object* x_125; lean_object* x_126; uint64_t x_127; lean_object* x_128; 
x_125 = l_Lean_Meta_simpGlobalConfig;
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get_uint64(x_125, sizeof(void*)*1);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
x_128 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_40);
lean_ctor_set(x_128, 2, x_41);
lean_ctor_set(x_128, 3, x_42);
lean_ctor_set(x_128, 4, x_43);
lean_ctor_set(x_128, 5, x_44);
lean_ctor_set(x_128, 6, x_45);
lean_ctor_set_uint64(x_128, sizeof(void*)*7, x_127);
lean_ctor_set_uint8(x_128, sizeof(void*)*7 + 8, x_39);
lean_ctor_set_uint8(x_128, sizeof(void*)*7 + 9, x_46);
lean_ctor_set_uint8(x_128, sizeof(void*)*7 + 10, x_47);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_129 = lean_mk_string_unchecked("Iff", 3, 3);
x_130 = l_Lean_Name_mkStr1(x_129);
x_131 = l_Lean_Expr_isAppOfArity(x_122, x_130, x_32);
lean_dec(x_130);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_132 = lean_mk_string_unchecked("Ne", 2, 2);
x_133 = l_Lean_Name_mkStr1(x_132);
x_134 = lean_unsigned_to_nat(3u);
x_135 = l_Lean_Expr_isAppOfArity(x_122, x_133, x_134);
lean_dec(x_133);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_136 = lean_mk_string_unchecked("Not", 3, 3);
x_137 = l_Lean_Name_mkStr1(x_136);
x_138 = lean_unsigned_to_nat(1u);
x_139 = l_Lean_Expr_isAppOfArity(x_122, x_137, x_138);
lean_dec(x_137);
if (x_139 == 0)
{
lean_object* x_140; 
x_140 = l_Lean_Meta_DiscrTree_mkPath(x_122, x_139, x_128, x_4, x_5, x_6, x_123);
lean_dec(x_128);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; 
x_141 = l_Lean_Expr_appArg_x21(x_122);
lean_dec(x_122);
x_142 = l_Lean_Meta_DiscrTree_mkPath(x_141, x_135, x_128, x_4, x_5, x_6, x_123);
lean_dec(x_128);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_143 = l_Lean_Expr_appFn_x21(x_122);
x_144 = l_Lean_Expr_appArg_x21(x_143);
lean_dec(x_143);
x_145 = l_Lean_Expr_appArg_x21(x_122);
lean_dec(x_122);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_128);
x_146 = l_Lean_Meta_mkEq(x_144, x_145, x_128, x_4, x_5, x_6, x_123);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = l_Lean_Meta_DiscrTree_mkPath(x_147, x_131, x_128, x_4, x_5, x_6, x_148);
lean_dec(x_128);
return x_149;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_128);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_150 = lean_ctor_get(x_146, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_146, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_152 = x_146;
} else {
 lean_dec_ref(x_146);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; lean_object* x_158; 
x_154 = l_Lean_Expr_appFn_x21(x_122);
lean_dec(x_122);
x_155 = l_Lean_Expr_appArg_x21(x_154);
lean_dec(x_154);
x_156 = lean_box(0);
x_157 = lean_unbox(x_156);
x_158 = l_Lean_Meta_DiscrTree_mkPath(x_155, x_157, x_128, x_4, x_5, x_6, x_123);
lean_dec(x_128);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; 
lean_dec(x_122);
x_159 = lean_ctor_get(x_124, 0);
lean_inc(x_159);
lean_dec(x_124);
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
lean_dec(x_159);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
lean_dec(x_160);
x_162 = lean_box(0);
x_163 = lean_unbox(x_162);
x_164 = l_Lean_Meta_DiscrTree_mkPath(x_161, x_163, x_128, x_4, x_5, x_6, x_123);
lean_dec(x_128);
return x_164;
}
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_free_object(x_51);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_179 = lean_ctor_get(x_121, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_121, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_181 = x_121;
} else {
 lean_dec_ref(x_121);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_179);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_183 = lean_ctor_get(x_51, 1);
lean_inc(x_183);
lean_dec(x_51);
x_184 = lean_ctor_get(x_50, 1);
lean_inc(x_184);
lean_dec(x_50);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_186 = x_183;
} else {
 lean_dec_ref(x_183);
 x_186 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_187 = l_Lean_Meta_whnfR(x_185, x_3, x_4, x_5, x_6, x_184);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
if (x_2 == 0)
{
lean_object* x_232; 
lean_dec(x_186);
x_232 = l_Lean_Meta_DiscrTree_mkPath(x_188, x_2, x_3, x_4, x_5, x_6, x_189);
return x_232;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; 
x_233 = lean_mk_string_unchecked("Eq", 2, 2);
x_234 = l_Lean_Name_mkStr1(x_233);
x_235 = lean_unsigned_to_nat(3u);
x_236 = l_Lean_Expr_isAppOfArity(x_188, x_234, x_235);
lean_dec(x_234);
if (x_236 == 0)
{
lean_object* x_237; 
lean_dec(x_186);
x_237 = lean_box(0);
x_190 = x_237;
goto block_231;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_238 = l_Lean_Expr_appFn_x21(x_188);
x_239 = l_Lean_Expr_appFn_x21(x_238);
x_240 = l_Lean_Expr_appArg_x21(x_239);
lean_dec(x_239);
x_241 = l_Lean_Expr_appArg_x21(x_238);
lean_dec(x_238);
x_242 = l_Lean_Expr_appArg_x21(x_188);
if (lean_is_scalar(x_186)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_186;
}
lean_ctor_set(x_243, 0, x_241);
lean_ctor_set(x_243, 1, x_242);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_240);
lean_ctor_set(x_244, 1, x_243);
x_245 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_245, 0, x_244);
x_190 = x_245;
goto block_231;
}
}
block_231:
{
lean_object* x_191; lean_object* x_192; uint64_t x_193; lean_object* x_194; 
x_191 = l_Lean_Meta_simpGlobalConfig;
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get_uint64(x_191, sizeof(void*)*1);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
x_194 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_40);
lean_ctor_set(x_194, 2, x_41);
lean_ctor_set(x_194, 3, x_42);
lean_ctor_set(x_194, 4, x_43);
lean_ctor_set(x_194, 5, x_44);
lean_ctor_set(x_194, 6, x_45);
lean_ctor_set_uint64(x_194, sizeof(void*)*7, x_193);
lean_ctor_set_uint8(x_194, sizeof(void*)*7 + 8, x_39);
lean_ctor_set_uint8(x_194, sizeof(void*)*7 + 9, x_46);
lean_ctor_set_uint8(x_194, sizeof(void*)*7 + 10, x_47);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_195; lean_object* x_196; uint8_t x_197; 
x_195 = lean_mk_string_unchecked("Iff", 3, 3);
x_196 = l_Lean_Name_mkStr1(x_195);
x_197 = l_Lean_Expr_isAppOfArity(x_188, x_196, x_32);
lean_dec(x_196);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; 
x_198 = lean_mk_string_unchecked("Ne", 2, 2);
x_199 = l_Lean_Name_mkStr1(x_198);
x_200 = lean_unsigned_to_nat(3u);
x_201 = l_Lean_Expr_isAppOfArity(x_188, x_199, x_200);
lean_dec(x_199);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_202 = lean_mk_string_unchecked("Not", 3, 3);
x_203 = l_Lean_Name_mkStr1(x_202);
x_204 = lean_unsigned_to_nat(1u);
x_205 = l_Lean_Expr_isAppOfArity(x_188, x_203, x_204);
lean_dec(x_203);
if (x_205 == 0)
{
lean_object* x_206; 
x_206 = l_Lean_Meta_DiscrTree_mkPath(x_188, x_205, x_194, x_4, x_5, x_6, x_189);
lean_dec(x_194);
return x_206;
}
else
{
lean_object* x_207; lean_object* x_208; 
x_207 = l_Lean_Expr_appArg_x21(x_188);
lean_dec(x_188);
x_208 = l_Lean_Meta_DiscrTree_mkPath(x_207, x_201, x_194, x_4, x_5, x_6, x_189);
lean_dec(x_194);
return x_208;
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_209 = l_Lean_Expr_appFn_x21(x_188);
x_210 = l_Lean_Expr_appArg_x21(x_209);
lean_dec(x_209);
x_211 = l_Lean_Expr_appArg_x21(x_188);
lean_dec(x_188);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_194);
x_212 = l_Lean_Meta_mkEq(x_210, x_211, x_194, x_4, x_5, x_6, x_189);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
x_215 = l_Lean_Meta_DiscrTree_mkPath(x_213, x_197, x_194, x_4, x_5, x_6, x_214);
lean_dec(x_194);
return x_215;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_194);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_216 = lean_ctor_get(x_212, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_212, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_218 = x_212;
} else {
 lean_dec_ref(x_212);
 x_218 = lean_box(0);
}
if (lean_is_scalar(x_218)) {
 x_219 = lean_alloc_ctor(1, 2, 0);
} else {
 x_219 = x_218;
}
lean_ctor_set(x_219, 0, x_216);
lean_ctor_set(x_219, 1, x_217);
return x_219;
}
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_224; 
x_220 = l_Lean_Expr_appFn_x21(x_188);
lean_dec(x_188);
x_221 = l_Lean_Expr_appArg_x21(x_220);
lean_dec(x_220);
x_222 = lean_box(0);
x_223 = lean_unbox(x_222);
x_224 = l_Lean_Meta_DiscrTree_mkPath(x_221, x_223, x_194, x_4, x_5, x_6, x_189);
lean_dec(x_194);
return x_224;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; lean_object* x_230; 
lean_dec(x_188);
x_225 = lean_ctor_get(x_190, 0);
lean_inc(x_225);
lean_dec(x_190);
x_226 = lean_ctor_get(x_225, 1);
lean_inc(x_226);
lean_dec(x_225);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
lean_dec(x_226);
x_228 = lean_box(0);
x_229 = lean_unbox(x_228);
x_230 = l_Lean_Meta_DiscrTree_mkPath(x_227, x_229, x_194, x_4, x_5, x_6, x_189);
lean_dec(x_194);
return x_230;
}
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_186);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_246 = lean_ctor_get(x_187, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_187, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_248 = x_187;
} else {
 lean_dec_ref(x_187);
 x_248 = lean_box(0);
}
if (lean_is_scalar(x_248)) {
 x_249 = lean_alloc_ctor(1, 2, 0);
} else {
 x_249 = x_248;
}
lean_ctor_set(x_249, 0, x_246);
lean_ctor_set(x_249, 1, x_247);
return x_249;
}
}
}
else
{
uint8_t x_250; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_250 = !lean_is_exclusive(x_50);
if (x_250 == 0)
{
return x_50;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_50, 0);
x_252 = lean_ctor_get(x_50, 1);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_50);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
return x_253;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_____private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
lean_inc(x_1);
x_16 = l_Lean_Environment_find_x3f(x_13, x_1, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_9);
x_17 = lean_mk_string_unchecked("unknown constant '", 18, 18);
x_18 = l_Lean_stringToMessageData(x_17);
lean_dec(x_17);
x_19 = lean_unbox(x_14);
x_20 = l_Lean_MessageData_ofConstName(x_1, x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_mk_string_unchecked("'", 1, 1);
x_23 = l_Lean_stringToMessageData(x_22);
lean_dec(x_22);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
return x_25;
}
else
{
lean_object* x_26; 
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_ctor_get(x_16, 0);
lean_inc(x_26);
lean_dec(x_16);
lean_ctor_set(x_9, 0, x_26);
return x_9;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_9, 0);
x_28 = lean_ctor_get(x_9, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_9);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_box(0);
x_31 = lean_unbox(x_30);
lean_inc(x_1);
x_32 = l_Lean_Environment_find_x3f(x_29, x_1, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_mk_string_unchecked("unknown constant '", 18, 18);
x_34 = l_Lean_stringToMessageData(x_33);
lean_dec(x_33);
x_35 = lean_unbox(x_30);
x_36 = l_Lean_MessageData_ofConstName(x_1, x_35);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_mk_string_unchecked("'", 1, 1);
x_39 = l_Lean_stringToMessageData(x_38);
lean_dec(x_38);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_28);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_2);
lean_dec(x_1);
x_42 = lean_ctor_get(x_32, 0);
lean_inc(x_42);
lean_dec(x_32);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_28);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_mk_string_unchecked("ident", 5, 5);
x_10 = l_Lean_Name_mkStr1(x_9);
lean_inc(x_1);
x_11 = l_Lean_Syntax_isOfKind(x_1, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_12 = lean_box(0);
x_13 = lean_box(1);
x_14 = lean_unbox(x_13);
x_15 = lean_unbox(x_13);
x_16 = l_Lean_Elab_Term_elabTerm(x_1, x_12, x_14, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_4, 2);
lean_inc(x_17);
x_18 = l_Lean_Syntax_getId(x_1);
x_19 = l_Lean_LocalContext_findFromUserName_x3f(x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
x_21 = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(x_1, x_20, x_6, x_7, x_8);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_getConstInfo___at_____private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_23);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = l_Lean_ConstantInfo_type(x_26);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_24, 0);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_24);
x_30 = l_Lean_ConstantInfo_type(x_28);
lean_dec(x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_24);
if (x_32 == 0)
{
return x_24;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_24, 0);
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_24);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_21);
if (x_36 == 0)
{
return x_21;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_21, 0);
x_38 = lean_ctor_get(x_21, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_21);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = lean_ctor_get(x_19, 0);
lean_inc(x_40);
lean_dec(x_19);
x_41 = lean_ctor_get(x_40, 3);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_8);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_____private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_getConstInfo___at_____private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
x_11 = l_Lean_log___at___Lean_logError___at___Lean_Elab_logException___at___Lean_Elab_withLogging___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore_spec__2_spec__2_spec__2_spec__2(x_1, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (x_1 == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_2, x_11);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = lean_unbox(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey(x_14, x_17, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Meta_DiscrTree_keysAsPattern(x_19, x_7, x_8, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_logInfo___at___Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__0(x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_18);
if (x_29 == 0)
{
return x_18;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_18, 0);
x_31 = lean_ctor_get(x_18, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_18);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_33 = !lean_is_exclusive(x_13);
if (x_33 == 0)
{
return x_13;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_13, 0);
x_35 = lean_ctor_get(x_13, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_13);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("Parser", 6, 6);
x_7 = lean_mk_string_unchecked("discrTreeKeyCmd", 15, 15);
x_8 = l_Lean_Name_mkStr3(x_5, x_6, x_7);
lean_inc(x_1);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
x_10 = lean_box(x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___lam__0___boxed), 9, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_1);
x_12 = l_Lean_Elab_Command_liftTermElabM___redArg(x_11, x_2, x_3, x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_logInfo___at___Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___lam__0(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("discrTreeKeyCmd", 15, 15);
lean_inc(x_3);
x_6 = l_Lean_Name_mkStr3(x_3, x_4, x_5);
x_7 = lean_mk_string_unchecked("Elab", 4, 4);
x_8 = lean_mk_string_unchecked("Tactic", 6, 6);
x_9 = lean_mk_string_unchecked("DiscrTreeKey", 12, 12);
x_10 = lean_mk_string_unchecked("evalDiscrTreeKeyCmd", 19, 19);
x_11 = l_Lean_Name_mkStr5(x_3, x_7, x_8, x_9, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___boxed), 4, 0);
x_13 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_6, x_11, x_12, x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___lam__0(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (x_1 == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_2, x_12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_14 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType(x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_17 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey(x_15, x_3, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Meta_DiscrTree_keysAsPattern(x_18, x_8, x_9, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_logInfo___at___Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__0(x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_22);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_17);
if (x_28 == 0)
{
return x_17;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_ctor_get(x_17, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_17);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_32 = !lean_is_exclusive(x_14);
if (x_32 == 0)
{
return x_14;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_14, 0);
x_34 = lean_ctor_get(x_14, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_14);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("Parser", 6, 6);
x_7 = lean_mk_string_unchecked("discrTreeSimpKeyCmd", 19, 19);
x_8 = l_Lean_Name_mkStr3(x_5, x_6, x_7);
lean_inc(x_1);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
x_10 = lean_box(1);
x_11 = lean_box(x_9);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___lam__0___boxed), 10, 3);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_1);
lean_closure_set(x_12, 2, x_10);
x_13 = l_Lean_Elab_Command_liftTermElabM___redArg(x_12, x_2, x_3, x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___lam__0(x_11, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("discrTreeSimpKeyCmd", 19, 19);
lean_inc(x_3);
x_6 = l_Lean_Name_mkStr3(x_3, x_4, x_5);
x_7 = lean_mk_string_unchecked("Elab", 4, 4);
x_8 = lean_mk_string_unchecked("Tactic", 6, 6);
x_9 = lean_mk_string_unchecked("DiscrTreeKey", 12, 12);
x_10 = lean_mk_string_unchecked("evalDiscrTreeSimpKeyCmd", 23, 23);
x_11 = l_Lean_Name_mkStr5(x_3, x_7, x_8, x_9, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___boxed), 4, 0);
x_13 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_6, x_11, x_12, x_1);
return x_13;
}
}
lean_object* initialize_Init_Tactics(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_SimpTheorems(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_DiscrTreeKey(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Tactics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_SimpTheorems(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
