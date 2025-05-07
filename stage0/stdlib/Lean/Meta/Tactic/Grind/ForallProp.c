// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.ForallProp
// Imports: Init.Grind.Lemmas Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.Internalize Lean.Meta.Tactic.Grind.Simp Lean.Meta.Tactic.Grind.EqResolution
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addNewRawFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_activateTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_eqResolution(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateExistsDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_alreadyInternalized___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_Meta_Grind_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1____x40_Lean_Meta_Tactic_Grind_ForallProp___hyg_2854_(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_3, x_4, x_12);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_unbox(x_51);
lean_dec(x_51);
if (x_52 == 0)
{
uint8_t x_53; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_50);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_50, 0);
lean_dec(x_54);
x_55 = lean_box(0);
lean_ctor_set(x_50, 0, x_55);
return x_50;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
lean_dec(x_50);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_50, 1);
lean_inc(x_59);
lean_dec(x_50);
lean_inc(x_2);
x_60 = l_Lean_Meta_Grind_isEqFalse(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_unbox(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
lean_inc(x_2);
x_64 = l_Lean_Meta_Grind_isEqTrue___redArg(x_2, x_4, x_7, x_10, x_11, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_unbox(x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_61);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
lean_inc(x_3);
x_68 = l_Lean_Meta_Grind_isEqTrue___redArg(x_3, x_4, x_7, x_10, x_11, x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_unbox(x_69);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
lean_inc(x_3);
x_72 = l_Lean_Meta_Grind_isEqFalse(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
lean_dec(x_73);
if (x_74 == 0)
{
x_13 = x_72;
goto block_49;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
lean_inc(x_1);
x_76 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_4, x_7, x_10, x_11, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_unbox(x_77);
lean_dec(x_77);
if (x_78 == 0)
{
x_13 = x_76;
goto block_49;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_80 = l_Lean_Meta_isProp(x_2, x_8, x_9, x_10, x_11, x_79);
x_13 = x_80;
goto block_49;
}
}
else
{
x_13 = x_76;
goto block_49;
}
}
}
else
{
x_13 = x_72;
goto block_49;
}
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_68, 1);
lean_inc(x_81);
lean_dec(x_68);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_82 = l_Lean_Meta_Grind_mkEqTrueProof(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_mk_string_unchecked("Lean", 4, 4);
x_86 = lean_mk_string_unchecked("Grind", 5, 5);
x_87 = lean_mk_string_unchecked("imp_eq_of_eq_true_right", 23, 23);
x_88 = l_Lean_Name_mkStr3(x_85, x_86, x_87);
x_89 = lean_box(0);
x_90 = l_Lean_Expr_const___override(x_88, x_89);
x_91 = l_Lean_mkApp3(x_90, x_2, x_3, x_83);
x_92 = l_Lean_Meta_Grind_pushEqTrue(x_1, x_91, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_84);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_92;
}
else
{
uint8_t x_93; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_82);
if (x_93 == 0)
{
return x_82;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_82, 0);
x_95 = lean_ctor_get(x_82, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_82);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_68);
if (x_97 == 0)
{
return x_68;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_68, 0);
x_99 = lean_ctor_get(x_68, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_68);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_64, 1);
lean_inc(x_101);
lean_dec(x_64);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_102 = l_Lean_Meta_Grind_mkEqTrueProof(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_101);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_mk_string_unchecked("Lean", 4, 4);
x_106 = lean_mk_string_unchecked("Grind", 5, 5);
x_107 = lean_mk_string_unchecked("imp_eq_of_eq_true_left", 22, 22);
x_108 = l_Lean_Name_mkStr3(x_105, x_106, x_107);
x_109 = lean_box(0);
x_110 = l_Lean_Expr_const___override(x_108, x_109);
lean_inc(x_3);
x_111 = l_Lean_mkApp3(x_110, x_2, x_3, x_103);
x_112 = lean_unbox(x_61);
lean_dec(x_61);
x_113 = l_Lean_Meta_Grind_pushEqCore(x_1, x_3, x_111, x_112, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_104);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_113;
}
else
{
uint8_t x_114; 
lean_dec(x_61);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_102);
if (x_114 == 0)
{
return x_102;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_102, 0);
x_116 = lean_ctor_get(x_102, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_102);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_61);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_64);
if (x_118 == 0)
{
return x_64;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_64, 0);
x_120 = lean_ctor_get(x_64, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_64);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
else
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_61);
x_122 = lean_ctor_get(x_60, 1);
lean_inc(x_122);
lean_dec(x_60);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_123 = l_Lean_Meta_Grind_mkEqFalseProof(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_122);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = lean_mk_string_unchecked("Lean", 4, 4);
x_127 = lean_mk_string_unchecked("Grind", 5, 5);
x_128 = lean_mk_string_unchecked("imp_eq_of_eq_false_left", 23, 23);
x_129 = l_Lean_Name_mkStr3(x_126, x_127, x_128);
x_130 = lean_box(0);
x_131 = l_Lean_Expr_const___override(x_129, x_130);
x_132 = l_Lean_mkApp3(x_131, x_2, x_3, x_124);
x_133 = l_Lean_Meta_Grind_pushEqTrue(x_1, x_132, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_125);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_133;
}
else
{
uint8_t x_134; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_134 = !lean_is_exclusive(x_123);
if (x_134 == 0)
{
return x_123;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_123, 0);
x_136 = lean_ctor_get(x_123, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_123);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
}
else
{
uint8_t x_138; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_138 = !lean_is_exclusive(x_60);
if (x_138 == 0)
{
return x_60;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_60, 0);
x_140 = lean_ctor_get(x_60, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_60);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
block_49:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_23 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_26 = l_Lean_Meta_Grind_mkEqFalseProof(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_mk_string_unchecked("Lean", 4, 4);
x_30 = lean_mk_string_unchecked("Grind", 5, 5);
x_31 = lean_mk_string_unchecked("eq_false_of_imp_eq_true", 23, 23);
x_32 = l_Lean_Name_mkStr3(x_29, x_30, x_31);
x_33 = lean_box(0);
x_34 = l_Lean_Expr_const___override(x_32, x_33);
lean_inc(x_2);
x_35 = l_Lean_mkApp4(x_34, x_2, x_3, x_24, x_27);
x_36 = l_Lean_Meta_Grind_pushEqFalse(x_2, x_35, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_28);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_24);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_26);
if (x_37 == 0)
{
return x_26;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_26, 0);
x_39 = lean_ctor_get(x_26, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_26);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_23);
if (x_41 == 0)
{
return x_23;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_23, 0);
x_43 = lean_ctor_get(x_23, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_23);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_13);
if (x_45 == 0)
{
return x_13;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_13, 0);
x_47 = lean_ctor_get(x_13, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_13);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_45 = lean_mk_string_unchecked("grind", 5, 5);
x_46 = lean_mk_string_unchecked("debug", 5, 5);
x_47 = lean_mk_string_unchecked("forallPropagator", 16, 16);
x_48 = l_Lean_Name_mkStr3(x_45, x_46, x_47);
lean_inc(x_48);
x_263 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_48, x_8, x_10);
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = lean_unbox(x_264);
lean_dec(x_264);
if (x_265 == 0)
{
lean_object* x_266; 
x_266 = lean_ctor_get(x_263, 1);
lean_inc(x_266);
lean_dec(x_263);
x_190 = x_2;
x_191 = x_3;
x_192 = x_4;
x_193 = x_5;
x_194 = x_6;
x_195 = x_7;
x_196 = x_8;
x_197 = x_9;
x_198 = x_266;
goto block_262;
}
else
{
uint8_t x_267; 
x_267 = !lean_is_exclusive(x_263);
if (x_267 == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_263, 1);
x_269 = lean_ctor_get(x_263, 0);
lean_dec(x_269);
x_270 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_268);
if (lean_obj_tag(x_270) == 0)
{
uint8_t x_271; 
x_271 = !lean_is_exclusive(x_270);
if (x_271 == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_272 = lean_ctor_get(x_270, 1);
x_273 = lean_ctor_get(x_270, 0);
lean_dec(x_273);
x_274 = lean_mk_string_unchecked("", 0, 0);
x_275 = l_Lean_stringToMessageData(x_274);
lean_dec(x_274);
lean_inc(x_1);
x_276 = l_Lean_MessageData_ofExpr(x_1);
lean_inc(x_275);
lean_ctor_set_tag(x_270, 7);
lean_ctor_set(x_270, 1, x_276);
lean_ctor_set(x_270, 0, x_275);
lean_ctor_set_tag(x_263, 7);
lean_ctor_set(x_263, 1, x_275);
lean_ctor_set(x_263, 0, x_270);
lean_inc(x_48);
x_277 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_48, x_263, x_6, x_7, x_8, x_9, x_272);
x_278 = lean_ctor_get(x_277, 1);
lean_inc(x_278);
lean_dec(x_277);
x_190 = x_2;
x_191 = x_3;
x_192 = x_4;
x_193 = x_5;
x_194 = x_6;
x_195 = x_7;
x_196 = x_8;
x_197 = x_9;
x_198 = x_278;
goto block_262;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_279 = lean_ctor_get(x_270, 1);
lean_inc(x_279);
lean_dec(x_270);
x_280 = lean_mk_string_unchecked("", 0, 0);
x_281 = l_Lean_stringToMessageData(x_280);
lean_dec(x_280);
lean_inc(x_1);
x_282 = l_Lean_MessageData_ofExpr(x_1);
lean_inc(x_281);
x_283 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_283, 0, x_281);
lean_ctor_set(x_283, 1, x_282);
lean_ctor_set_tag(x_263, 7);
lean_ctor_set(x_263, 1, x_281);
lean_ctor_set(x_263, 0, x_283);
lean_inc(x_48);
x_284 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_48, x_263, x_6, x_7, x_8, x_9, x_279);
x_285 = lean_ctor_get(x_284, 1);
lean_inc(x_285);
lean_dec(x_284);
x_190 = x_2;
x_191 = x_3;
x_192 = x_4;
x_193 = x_5;
x_194 = x_6;
x_195 = x_7;
x_196 = x_8;
x_197 = x_9;
x_198 = x_285;
goto block_262;
}
}
else
{
lean_free_object(x_263);
lean_dec(x_48);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_270;
}
}
else
{
lean_object* x_286; lean_object* x_287; 
x_286 = lean_ctor_get(x_263, 1);
lean_inc(x_286);
lean_dec(x_263);
x_287 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_286);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_288 = lean_ctor_get(x_287, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 x_289 = x_287;
} else {
 lean_dec_ref(x_287);
 x_289 = lean_box(0);
}
x_290 = lean_mk_string_unchecked("", 0, 0);
x_291 = l_Lean_stringToMessageData(x_290);
lean_dec(x_290);
lean_inc(x_1);
x_292 = l_Lean_MessageData_ofExpr(x_1);
lean_inc(x_291);
if (lean_is_scalar(x_289)) {
 x_293 = lean_alloc_ctor(7, 2, 0);
} else {
 x_293 = x_289;
 lean_ctor_set_tag(x_293, 7);
}
lean_ctor_set(x_293, 0, x_291);
lean_ctor_set(x_293, 1, x_292);
x_294 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_291);
lean_inc(x_48);
x_295 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_48, x_294, x_6, x_7, x_8, x_9, x_288);
x_296 = lean_ctor_get(x_295, 1);
lean_inc(x_296);
lean_dec(x_295);
x_190 = x_2;
x_191 = x_3;
x_192 = x_4;
x_193 = x_5;
x_194 = x_6;
x_195 = x_7;
x_196 = x_8;
x_197 = x_9;
x_198 = x_296;
goto block_262;
}
else
{
lean_dec(x_48);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_287;
}
}
}
block_44:
{
lean_object* x_29; 
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
x_29 = l_Lean_Meta_Simp_Result_getProof(x_18, x_24, x_25, x_26, x_27, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_mk_string_unchecked("Lean", 4, 4);
x_33 = lean_mk_string_unchecked("Grind", 5, 5);
x_34 = lean_mk_string_unchecked("forall_propagator", 17, 17);
x_35 = l_Lean_Name_mkStr3(x_32, x_33, x_34);
x_36 = lean_box(0);
x_37 = l_Lean_Expr_const___override(x_35, x_36);
lean_inc(x_15);
x_38 = l_Lean_mkApp5(x_37, x_12, x_19, x_15, x_16, x_30);
x_39 = l_Lean_Meta_Grind_pushEqCore(x_1, x_15, x_38, x_17, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_31);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
return x_39;
}
else
{
uint8_t x_40; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_29);
if (x_40 == 0)
{
return x_29;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_29, 0);
x_42 = lean_ctor_get(x_29, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_29);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
block_189:
{
lean_object* x_59; 
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_12);
x_59 = l_Lean_Meta_Grind_mkEqTrueProof(x_12, x_50, x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_inc(x_60);
lean_inc(x_12);
x_62 = l_Lean_Meta_mkOfEqTrueCore(x_12, x_60);
x_63 = lean_expr_instantiate1(x_13, x_62);
lean_dec(x_62);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_64 = l_Lean_Meta_Grind_preprocess(x_63, x_50, x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_61);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_50, x_66);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = lean_ctor_get(x_67, 1);
x_71 = lean_ctor_get(x_65, 0);
lean_inc(x_71);
x_72 = lean_box(0);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_71);
x_73 = lean_grind_internalize(x_71, x_69, x_72, x_50, x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_70);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_75 = lean_ctor_get(x_73, 1);
x_76 = lean_ctor_get(x_73, 0);
lean_dec(x_76);
lean_inc(x_48);
x_77 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_48, x_56, x_75);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_79 = lean_ctor_get(x_77, 0);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_12);
x_81 = l_Lean_Expr_lam___override(x_11, x_12, x_13, x_14);
x_82 = lean_unbox(x_79);
lean_dec(x_79);
if (x_82 == 0)
{
lean_free_object(x_77);
lean_free_object(x_73);
lean_free_object(x_67);
lean_dec(x_48);
x_15 = x_71;
x_16 = x_60;
x_17 = x_49;
x_18 = x_65;
x_19 = x_81;
x_20 = x_50;
x_21 = x_51;
x_22 = x_52;
x_23 = x_53;
x_24 = x_54;
x_25 = x_55;
x_26 = x_56;
x_27 = x_57;
x_28 = x_80;
goto block_44;
}
else
{
lean_object* x_83; 
x_83 = l_Lean_Meta_Grind_updateLastTag(x_50, x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_80);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_85 = lean_ctor_get(x_83, 1);
x_86 = lean_ctor_get(x_83, 0);
lean_dec(x_86);
x_87 = lean_mk_string_unchecked("q': ", 4, 4);
x_88 = l_Lean_stringToMessageData(x_87);
lean_dec(x_87);
lean_inc(x_71);
x_89 = l_Lean_MessageData_ofExpr(x_71);
lean_ctor_set_tag(x_83, 7);
lean_ctor_set(x_83, 1, x_89);
lean_ctor_set(x_83, 0, x_88);
x_90 = lean_mk_string_unchecked(" for", 4, 4);
x_91 = l_Lean_stringToMessageData(x_90);
lean_dec(x_90);
lean_ctor_set_tag(x_77, 7);
lean_ctor_set(x_77, 1, x_91);
lean_ctor_set(x_77, 0, x_83);
lean_inc(x_1);
x_92 = l_Lean_indentExpr(x_1);
lean_ctor_set_tag(x_73, 7);
lean_ctor_set(x_73, 1, x_92);
lean_ctor_set(x_73, 0, x_77);
x_93 = lean_mk_string_unchecked("", 0, 0);
x_94 = l_Lean_stringToMessageData(x_93);
lean_dec(x_93);
lean_ctor_set_tag(x_67, 7);
lean_ctor_set(x_67, 1, x_94);
lean_ctor_set(x_67, 0, x_73);
x_95 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_48, x_67, x_54, x_55, x_56, x_57, x_85);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
x_15 = x_71;
x_16 = x_60;
x_17 = x_49;
x_18 = x_65;
x_19 = x_81;
x_20 = x_50;
x_21 = x_51;
x_22 = x_52;
x_23 = x_53;
x_24 = x_54;
x_25 = x_55;
x_26 = x_56;
x_27 = x_57;
x_28 = x_96;
goto block_44;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_97 = lean_ctor_get(x_83, 1);
lean_inc(x_97);
lean_dec(x_83);
x_98 = lean_mk_string_unchecked("q': ", 4, 4);
x_99 = l_Lean_stringToMessageData(x_98);
lean_dec(x_98);
lean_inc(x_71);
x_100 = l_Lean_MessageData_ofExpr(x_71);
x_101 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_mk_string_unchecked(" for", 4, 4);
x_103 = l_Lean_stringToMessageData(x_102);
lean_dec(x_102);
lean_ctor_set_tag(x_77, 7);
lean_ctor_set(x_77, 1, x_103);
lean_ctor_set(x_77, 0, x_101);
lean_inc(x_1);
x_104 = l_Lean_indentExpr(x_1);
lean_ctor_set_tag(x_73, 7);
lean_ctor_set(x_73, 1, x_104);
lean_ctor_set(x_73, 0, x_77);
x_105 = lean_mk_string_unchecked("", 0, 0);
x_106 = l_Lean_stringToMessageData(x_105);
lean_dec(x_105);
lean_ctor_set_tag(x_67, 7);
lean_ctor_set(x_67, 1, x_106);
lean_ctor_set(x_67, 0, x_73);
x_107 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_48, x_67, x_54, x_55, x_56, x_57, x_97);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
x_15 = x_71;
x_16 = x_60;
x_17 = x_49;
x_18 = x_65;
x_19 = x_81;
x_20 = x_50;
x_21 = x_51;
x_22 = x_52;
x_23 = x_53;
x_24 = x_54;
x_25 = x_55;
x_26 = x_56;
x_27 = x_57;
x_28 = x_108;
goto block_44;
}
}
else
{
lean_dec(x_81);
lean_free_object(x_77);
lean_free_object(x_73);
lean_dec(x_71);
lean_free_object(x_67);
lean_dec(x_65);
lean_dec(x_60);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_12);
lean_dec(x_1);
return x_83;
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_109 = lean_ctor_get(x_77, 0);
x_110 = lean_ctor_get(x_77, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_77);
lean_inc(x_12);
x_111 = l_Lean_Expr_lam___override(x_11, x_12, x_13, x_14);
x_112 = lean_unbox(x_109);
lean_dec(x_109);
if (x_112 == 0)
{
lean_free_object(x_73);
lean_free_object(x_67);
lean_dec(x_48);
x_15 = x_71;
x_16 = x_60;
x_17 = x_49;
x_18 = x_65;
x_19 = x_111;
x_20 = x_50;
x_21 = x_51;
x_22 = x_52;
x_23 = x_53;
x_24 = x_54;
x_25 = x_55;
x_26 = x_56;
x_27 = x_57;
x_28 = x_110;
goto block_44;
}
else
{
lean_object* x_113; 
x_113 = l_Lean_Meta_Grind_updateLastTag(x_50, x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_110);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_115 = x_113;
} else {
 lean_dec_ref(x_113);
 x_115 = lean_box(0);
}
x_116 = lean_mk_string_unchecked("q': ", 4, 4);
x_117 = l_Lean_stringToMessageData(x_116);
lean_dec(x_116);
lean_inc(x_71);
x_118 = l_Lean_MessageData_ofExpr(x_71);
if (lean_is_scalar(x_115)) {
 x_119 = lean_alloc_ctor(7, 2, 0);
} else {
 x_119 = x_115;
 lean_ctor_set_tag(x_119, 7);
}
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_mk_string_unchecked(" for", 4, 4);
x_121 = l_Lean_stringToMessageData(x_120);
lean_dec(x_120);
x_122 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_121);
lean_inc(x_1);
x_123 = l_Lean_indentExpr(x_1);
lean_ctor_set_tag(x_73, 7);
lean_ctor_set(x_73, 1, x_123);
lean_ctor_set(x_73, 0, x_122);
x_124 = lean_mk_string_unchecked("", 0, 0);
x_125 = l_Lean_stringToMessageData(x_124);
lean_dec(x_124);
lean_ctor_set_tag(x_67, 7);
lean_ctor_set(x_67, 1, x_125);
lean_ctor_set(x_67, 0, x_73);
x_126 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_48, x_67, x_54, x_55, x_56, x_57, x_114);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
lean_dec(x_126);
x_15 = x_71;
x_16 = x_60;
x_17 = x_49;
x_18 = x_65;
x_19 = x_111;
x_20 = x_50;
x_21 = x_51;
x_22 = x_52;
x_23 = x_53;
x_24 = x_54;
x_25 = x_55;
x_26 = x_56;
x_27 = x_57;
x_28 = x_127;
goto block_44;
}
else
{
lean_dec(x_111);
lean_free_object(x_73);
lean_dec(x_71);
lean_free_object(x_67);
lean_dec(x_65);
lean_dec(x_60);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_12);
lean_dec(x_1);
return x_113;
}
}
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_128 = lean_ctor_get(x_73, 1);
lean_inc(x_128);
lean_dec(x_73);
lean_inc(x_48);
x_129 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_48, x_56, x_128);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_132 = x_129;
} else {
 lean_dec_ref(x_129);
 x_132 = lean_box(0);
}
lean_inc(x_12);
x_133 = l_Lean_Expr_lam___override(x_11, x_12, x_13, x_14);
x_134 = lean_unbox(x_130);
lean_dec(x_130);
if (x_134 == 0)
{
lean_dec(x_132);
lean_free_object(x_67);
lean_dec(x_48);
x_15 = x_71;
x_16 = x_60;
x_17 = x_49;
x_18 = x_65;
x_19 = x_133;
x_20 = x_50;
x_21 = x_51;
x_22 = x_52;
x_23 = x_53;
x_24 = x_54;
x_25 = x_55;
x_26 = x_56;
x_27 = x_57;
x_28 = x_131;
goto block_44;
}
else
{
lean_object* x_135; 
x_135 = l_Lean_Meta_Grind_updateLastTag(x_50, x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_131);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_137 = x_135;
} else {
 lean_dec_ref(x_135);
 x_137 = lean_box(0);
}
x_138 = lean_mk_string_unchecked("q': ", 4, 4);
x_139 = l_Lean_stringToMessageData(x_138);
lean_dec(x_138);
lean_inc(x_71);
x_140 = l_Lean_MessageData_ofExpr(x_71);
if (lean_is_scalar(x_137)) {
 x_141 = lean_alloc_ctor(7, 2, 0);
} else {
 x_141 = x_137;
 lean_ctor_set_tag(x_141, 7);
}
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
x_142 = lean_mk_string_unchecked(" for", 4, 4);
x_143 = l_Lean_stringToMessageData(x_142);
lean_dec(x_142);
if (lean_is_scalar(x_132)) {
 x_144 = lean_alloc_ctor(7, 2, 0);
} else {
 x_144 = x_132;
 lean_ctor_set_tag(x_144, 7);
}
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_143);
lean_inc(x_1);
x_145 = l_Lean_indentExpr(x_1);
x_146 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
x_147 = lean_mk_string_unchecked("", 0, 0);
x_148 = l_Lean_stringToMessageData(x_147);
lean_dec(x_147);
lean_ctor_set_tag(x_67, 7);
lean_ctor_set(x_67, 1, x_148);
lean_ctor_set(x_67, 0, x_146);
x_149 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_48, x_67, x_54, x_55, x_56, x_57, x_136);
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
x_15 = x_71;
x_16 = x_60;
x_17 = x_49;
x_18 = x_65;
x_19 = x_133;
x_20 = x_50;
x_21 = x_51;
x_22 = x_52;
x_23 = x_53;
x_24 = x_54;
x_25 = x_55;
x_26 = x_56;
x_27 = x_57;
x_28 = x_150;
goto block_44;
}
else
{
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_71);
lean_free_object(x_67);
lean_dec(x_65);
lean_dec(x_60);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_12);
lean_dec(x_1);
return x_135;
}
}
}
}
else
{
lean_dec(x_71);
lean_free_object(x_67);
lean_dec(x_65);
lean_dec(x_60);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
return x_73;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_151 = lean_ctor_get(x_67, 0);
x_152 = lean_ctor_get(x_67, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_67);
x_153 = lean_ctor_get(x_65, 0);
lean_inc(x_153);
x_154 = lean_box(0);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_153);
x_155 = lean_grind_internalize(x_153, x_151, x_154, x_50, x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_152);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_157 = x_155;
} else {
 lean_dec_ref(x_155);
 x_157 = lean_box(0);
}
lean_inc(x_48);
x_158 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_48, x_56, x_156);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_161 = x_158;
} else {
 lean_dec_ref(x_158);
 x_161 = lean_box(0);
}
lean_inc(x_12);
x_162 = l_Lean_Expr_lam___override(x_11, x_12, x_13, x_14);
x_163 = lean_unbox(x_159);
lean_dec(x_159);
if (x_163 == 0)
{
lean_dec(x_161);
lean_dec(x_157);
lean_dec(x_48);
x_15 = x_153;
x_16 = x_60;
x_17 = x_49;
x_18 = x_65;
x_19 = x_162;
x_20 = x_50;
x_21 = x_51;
x_22 = x_52;
x_23 = x_53;
x_24 = x_54;
x_25 = x_55;
x_26 = x_56;
x_27 = x_57;
x_28 = x_160;
goto block_44;
}
else
{
lean_object* x_164; 
x_164 = l_Lean_Meta_Grind_updateLastTag(x_50, x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_160);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_166 = x_164;
} else {
 lean_dec_ref(x_164);
 x_166 = lean_box(0);
}
x_167 = lean_mk_string_unchecked("q': ", 4, 4);
x_168 = l_Lean_stringToMessageData(x_167);
lean_dec(x_167);
lean_inc(x_153);
x_169 = l_Lean_MessageData_ofExpr(x_153);
if (lean_is_scalar(x_166)) {
 x_170 = lean_alloc_ctor(7, 2, 0);
} else {
 x_170 = x_166;
 lean_ctor_set_tag(x_170, 7);
}
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
x_171 = lean_mk_string_unchecked(" for", 4, 4);
x_172 = l_Lean_stringToMessageData(x_171);
lean_dec(x_171);
if (lean_is_scalar(x_161)) {
 x_173 = lean_alloc_ctor(7, 2, 0);
} else {
 x_173 = x_161;
 lean_ctor_set_tag(x_173, 7);
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_172);
lean_inc(x_1);
x_174 = l_Lean_indentExpr(x_1);
if (lean_is_scalar(x_157)) {
 x_175 = lean_alloc_ctor(7, 2, 0);
} else {
 x_175 = x_157;
 lean_ctor_set_tag(x_175, 7);
}
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
x_176 = lean_mk_string_unchecked("", 0, 0);
x_177 = l_Lean_stringToMessageData(x_176);
lean_dec(x_176);
x_178 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_177);
x_179 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_48, x_178, x_54, x_55, x_56, x_57, x_165);
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
lean_dec(x_179);
x_15 = x_153;
x_16 = x_60;
x_17 = x_49;
x_18 = x_65;
x_19 = x_162;
x_20 = x_50;
x_21 = x_51;
x_22 = x_52;
x_23 = x_53;
x_24 = x_54;
x_25 = x_55;
x_26 = x_56;
x_27 = x_57;
x_28 = x_180;
goto block_44;
}
else
{
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_157);
lean_dec(x_153);
lean_dec(x_65);
lean_dec(x_60);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_12);
lean_dec(x_1);
return x_164;
}
}
}
else
{
lean_dec(x_153);
lean_dec(x_65);
lean_dec(x_60);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
return x_155;
}
}
}
else
{
uint8_t x_181; 
lean_dec(x_60);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_181 = !lean_is_exclusive(x_64);
if (x_181 == 0)
{
return x_64;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_64, 0);
x_183 = lean_ctor_get(x_64, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_64);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
else
{
uint8_t x_185; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_185 = !lean_is_exclusive(x_59);
if (x_185 == 0)
{
return x_59;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_59, 0);
x_187 = lean_ctor_get(x_59, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_59);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
}
block_262:
{
uint8_t x_199; 
x_199 = l_Lean_Expr_hasLooseBVars(x_13);
if (x_199 == 0)
{
lean_object* x_200; 
lean_dec(x_48);
lean_dec(x_11);
x_200 = l_Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp(x_1, x_12, x_13, x_190, x_191, x_192, x_193, x_194, x_195, x_196, x_197, x_198);
return x_200;
}
else
{
lean_object* x_201; 
lean_inc(x_12);
x_201 = l_Lean_Meta_Grind_isEqTrue___redArg(x_12, x_190, x_193, x_196, x_197, x_198);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; uint8_t x_203; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_unbox(x_202);
lean_dec(x_202);
if (x_203 == 0)
{
uint8_t x_204; 
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_48);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_204 = !lean_is_exclusive(x_201);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_201, 0);
lean_dec(x_205);
x_206 = lean_box(0);
lean_ctor_set(x_201, 0, x_206);
return x_201;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_201, 1);
lean_inc(x_207);
lean_dec(x_201);
x_208 = lean_box(0);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_207);
return x_209;
}
}
else
{
lean_object* x_210; lean_object* x_211; uint8_t x_212; 
x_210 = lean_ctor_get(x_201, 1);
lean_inc(x_210);
lean_dec(x_201);
lean_inc(x_48);
x_211 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_48, x_196, x_210);
x_212 = !lean_is_exclusive(x_211);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_213 = lean_ctor_get(x_211, 0);
x_214 = lean_ctor_get(x_211, 1);
x_215 = lean_box(0);
x_216 = lean_unbox(x_213);
lean_dec(x_213);
if (x_216 == 0)
{
uint8_t x_217; 
lean_free_object(x_211);
x_217 = lean_unbox(x_215);
x_49 = x_217;
x_50 = x_190;
x_51 = x_191;
x_52 = x_192;
x_53 = x_193;
x_54 = x_194;
x_55 = x_195;
x_56 = x_196;
x_57 = x_197;
x_58 = x_214;
goto block_189;
}
else
{
lean_object* x_218; 
x_218 = l_Lean_Meta_Grind_updateLastTag(x_190, x_191, x_192, x_193, x_194, x_195, x_196, x_197, x_214);
if (lean_obj_tag(x_218) == 0)
{
uint8_t x_219; 
x_219 = !lean_is_exclusive(x_218);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; 
x_220 = lean_ctor_get(x_218, 1);
x_221 = lean_ctor_get(x_218, 0);
lean_dec(x_221);
x_222 = lean_mk_string_unchecked("isEqTrue, ", 10, 10);
x_223 = l_Lean_stringToMessageData(x_222);
lean_dec(x_222);
lean_inc(x_1);
x_224 = l_Lean_MessageData_ofExpr(x_1);
lean_ctor_set_tag(x_218, 7);
lean_ctor_set(x_218, 1, x_224);
lean_ctor_set(x_218, 0, x_223);
x_225 = lean_mk_string_unchecked("", 0, 0);
x_226 = l_Lean_stringToMessageData(x_225);
lean_dec(x_225);
lean_ctor_set_tag(x_211, 7);
lean_ctor_set(x_211, 1, x_226);
lean_ctor_set(x_211, 0, x_218);
lean_inc(x_48);
x_227 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_48, x_211, x_194, x_195, x_196, x_197, x_220);
x_228 = lean_ctor_get(x_227, 1);
lean_inc(x_228);
lean_dec(x_227);
x_229 = lean_unbox(x_215);
x_49 = x_229;
x_50 = x_190;
x_51 = x_191;
x_52 = x_192;
x_53 = x_193;
x_54 = x_194;
x_55 = x_195;
x_56 = x_196;
x_57 = x_197;
x_58 = x_228;
goto block_189;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; 
x_230 = lean_ctor_get(x_218, 1);
lean_inc(x_230);
lean_dec(x_218);
x_231 = lean_mk_string_unchecked("isEqTrue, ", 10, 10);
x_232 = l_Lean_stringToMessageData(x_231);
lean_dec(x_231);
lean_inc(x_1);
x_233 = l_Lean_MessageData_ofExpr(x_1);
x_234 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
x_235 = lean_mk_string_unchecked("", 0, 0);
x_236 = l_Lean_stringToMessageData(x_235);
lean_dec(x_235);
lean_ctor_set_tag(x_211, 7);
lean_ctor_set(x_211, 1, x_236);
lean_ctor_set(x_211, 0, x_234);
lean_inc(x_48);
x_237 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_48, x_211, x_194, x_195, x_196, x_197, x_230);
x_238 = lean_ctor_get(x_237, 1);
lean_inc(x_238);
lean_dec(x_237);
x_239 = lean_unbox(x_215);
x_49 = x_239;
x_50 = x_190;
x_51 = x_191;
x_52 = x_192;
x_53 = x_193;
x_54 = x_194;
x_55 = x_195;
x_56 = x_196;
x_57 = x_197;
x_58 = x_238;
goto block_189;
}
}
else
{
lean_free_object(x_211);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_48);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
return x_218;
}
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; 
x_240 = lean_ctor_get(x_211, 0);
x_241 = lean_ctor_get(x_211, 1);
lean_inc(x_241);
lean_inc(x_240);
lean_dec(x_211);
x_242 = lean_box(0);
x_243 = lean_unbox(x_240);
lean_dec(x_240);
if (x_243 == 0)
{
uint8_t x_244; 
x_244 = lean_unbox(x_242);
x_49 = x_244;
x_50 = x_190;
x_51 = x_191;
x_52 = x_192;
x_53 = x_193;
x_54 = x_194;
x_55 = x_195;
x_56 = x_196;
x_57 = x_197;
x_58 = x_241;
goto block_189;
}
else
{
lean_object* x_245; 
x_245 = l_Lean_Meta_Grind_updateLastTag(x_190, x_191, x_192, x_193, x_194, x_195, x_196, x_197, x_241);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; 
x_246 = lean_ctor_get(x_245, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_247 = x_245;
} else {
 lean_dec_ref(x_245);
 x_247 = lean_box(0);
}
x_248 = lean_mk_string_unchecked("isEqTrue, ", 10, 10);
x_249 = l_Lean_stringToMessageData(x_248);
lean_dec(x_248);
lean_inc(x_1);
x_250 = l_Lean_MessageData_ofExpr(x_1);
if (lean_is_scalar(x_247)) {
 x_251 = lean_alloc_ctor(7, 2, 0);
} else {
 x_251 = x_247;
 lean_ctor_set_tag(x_251, 7);
}
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
x_252 = lean_mk_string_unchecked("", 0, 0);
x_253 = l_Lean_stringToMessageData(x_252);
lean_dec(x_252);
x_254 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_254, 0, x_251);
lean_ctor_set(x_254, 1, x_253);
lean_inc(x_48);
x_255 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_48, x_254, x_194, x_195, x_196, x_197, x_246);
x_256 = lean_ctor_get(x_255, 1);
lean_inc(x_256);
lean_dec(x_255);
x_257 = lean_unbox(x_242);
x_49 = x_257;
x_50 = x_190;
x_51 = x_191;
x_52 = x_192;
x_53 = x_193;
x_54 = x_194;
x_55 = x_195;
x_56 = x_196;
x_57 = x_197;
x_58 = x_256;
goto block_189;
}
else
{
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_48);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
return x_245;
}
}
}
}
}
else
{
uint8_t x_258; 
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_48);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_258 = !lean_is_exclusive(x_201);
if (x_258 == 0)
{
return x_201;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_201, 0);
x_260 = lean_ctor_get(x_201, 1);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_201);
x_261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_261, 0, x_259);
lean_ctor_set(x_261, 1, x_260);
return x_261;
}
}
}
}
}
else
{
lean_object* x_297; lean_object* x_298; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_297 = lean_box(0);
x_298 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_298, 1, x_10);
return x_298;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
lean_inc(x_2);
x_5 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_6 = l_Lean_Expr_isApp(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_2);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = l_Lean_Expr_appFnCleanup___redArg(x_5);
x_9 = lean_mk_string_unchecked("eq_true", 7, 7);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = l_Lean_Expr_isConstOf(x_8, x_10);
lean_dec(x_10);
lean_dec(x_8);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_box(0);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_13);
x_16 = lean_box(0);
return x_16;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_mk_empty_array_with_capacity(x_9);
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
x_13 = l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(x_1, x_10, x_2, x_3, x_12, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_24; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
x_24 = l_Lean_Exception_isInterrupt(x_14);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = l_Lean_Exception_isRuntime(x_14);
lean_dec(x_14);
x_16 = x_25;
goto block_23;
}
else
{
lean_dec(x_14);
x_16 = x_24;
goto block_23;
}
block_23:
{
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_13, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set_tag(x_13, 0);
lean_ctor_set(x_13, 0, x_20);
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_13);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_15);
return x_22;
}
}
else
{
lean_dec(x_15);
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_134; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_134 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_174; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
lean_inc(x_135);
x_174 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f(x_135);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_175 = lean_st_ref_take(x_2, x_136);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = lean_ctor_get(x_176, 12);
lean_inc(x_178);
x_179 = lean_ctor_get(x_178, 7);
lean_inc(x_179);
x_180 = lean_ctor_get(x_176, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_176, 1);
lean_inc(x_181);
x_182 = lean_ctor_get(x_176, 2);
lean_inc(x_182);
x_183 = lean_ctor_get(x_176, 3);
lean_inc(x_183);
x_184 = lean_ctor_get(x_176, 4);
lean_inc(x_184);
x_185 = lean_ctor_get(x_176, 5);
lean_inc(x_185);
x_186 = lean_ctor_get(x_176, 6);
lean_inc(x_186);
x_187 = lean_ctor_get(x_176, 7);
lean_inc(x_187);
x_188 = lean_ctor_get_uint8(x_176, sizeof(void*)*16);
x_189 = lean_ctor_get(x_176, 8);
lean_inc(x_189);
x_190 = lean_ctor_get(x_176, 9);
lean_inc(x_190);
x_191 = lean_ctor_get(x_176, 10);
lean_inc(x_191);
x_192 = lean_ctor_get(x_176, 11);
lean_inc(x_192);
x_193 = lean_ctor_get(x_178, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_178, 1);
lean_inc(x_194);
x_195 = lean_ctor_get(x_178, 2);
lean_inc(x_195);
x_196 = lean_ctor_get(x_178, 3);
lean_inc(x_196);
x_197 = lean_ctor_get(x_178, 4);
lean_inc(x_197);
x_198 = lean_ctor_get(x_178, 5);
lean_inc(x_198);
x_199 = lean_ctor_get(x_178, 6);
lean_inc(x_199);
x_200 = lean_unsigned_to_nat(1u);
x_201 = lean_nat_add(x_179, x_200);
x_202 = lean_ctor_get(x_178, 8);
lean_inc(x_202);
lean_dec(x_178);
x_203 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_203, 0, x_193);
lean_ctor_set(x_203, 1, x_194);
lean_ctor_set(x_203, 2, x_195);
lean_ctor_set(x_203, 3, x_196);
lean_ctor_set(x_203, 4, x_197);
lean_ctor_set(x_203, 5, x_198);
lean_ctor_set(x_203, 6, x_199);
lean_ctor_set(x_203, 7, x_201);
lean_ctor_set(x_203, 8, x_202);
x_204 = lean_ctor_get(x_176, 13);
lean_inc(x_204);
x_205 = lean_ctor_get(x_176, 14);
lean_inc(x_205);
x_206 = lean_ctor_get(x_176, 15);
lean_inc(x_206);
lean_dec(x_176);
x_207 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_207, 0, x_180);
lean_ctor_set(x_207, 1, x_181);
lean_ctor_set(x_207, 2, x_182);
lean_ctor_set(x_207, 3, x_183);
lean_ctor_set(x_207, 4, x_184);
lean_ctor_set(x_207, 5, x_185);
lean_ctor_set(x_207, 6, x_186);
lean_ctor_set(x_207, 7, x_187);
lean_ctor_set(x_207, 8, x_189);
lean_ctor_set(x_207, 9, x_190);
lean_ctor_set(x_207, 10, x_191);
lean_ctor_set(x_207, 11, x_192);
lean_ctor_set(x_207, 12, x_203);
lean_ctor_set(x_207, 13, x_204);
lean_ctor_set(x_207, 14, x_205);
lean_ctor_set(x_207, 15, x_206);
lean_ctor_set_uint8(x_207, sizeof(void*)*16, x_188);
x_208 = lean_st_ref_set(x_2, x_207, x_177);
x_209 = lean_ctor_get(x_208, 1);
lean_inc(x_209);
lean_dec(x_208);
x_210 = lean_mk_string_unchecked("local", 5, 5);
x_211 = l_Lean_Name_mkStr1(x_210);
x_212 = lean_name_append_index_after(x_211, x_179);
x_213 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_213, 0, x_212);
x_137 = x_213;
x_138 = x_2;
x_139 = x_3;
x_140 = x_4;
x_141 = x_5;
x_142 = x_6;
x_143 = x_7;
x_144 = x_8;
x_145 = x_9;
x_146 = x_209;
goto block_173;
}
else
{
uint8_t x_214; 
x_214 = !lean_is_exclusive(x_174);
if (x_214 == 0)
{
x_137 = x_174;
x_138 = x_2;
x_139 = x_3;
x_140 = x_4;
x_141 = x_5;
x_142 = x_6;
x_143 = x_7;
x_144 = x_8;
x_145 = x_9;
x_146 = x_136;
goto block_173;
}
else
{
lean_object* x_215; lean_object* x_216; 
x_215 = lean_ctor_get(x_174, 0);
lean_inc(x_215);
lean_dec(x_174);
x_216 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_216, 0, x_215);
x_137 = x_216;
x_138 = x_2;
x_139 = x_3;
x_140 = x_4;
x_141 = x_5;
x_142 = x_6;
x_143 = x_7;
x_144 = x_8;
x_145 = x_9;
x_146 = x_136;
goto block_173;
}
}
block_173:
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; 
x_147 = lean_st_ref_get(x_138, x_146);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_138, x_149);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
lean_inc(x_1);
x_153 = l_Lean_Meta_mkOfEqTrueCore(x_1, x_135);
x_154 = lean_box(6);
x_155 = lean_unbox(x_154);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_153);
lean_inc(x_137);
x_156 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(x_137, x_153, x_155, x_142, x_143, x_144, x_145, x_152);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = lean_ctor_get(x_148, 12);
lean_inc(x_159);
lean_dec(x_148);
x_160 = lean_ctor_get(x_159, 3);
lean_inc(x_160);
lean_dec(x_159);
x_161 = lean_ctor_get(x_160, 2);
lean_inc(x_161);
lean_dec(x_160);
x_107 = x_153;
x_108 = x_137;
x_109 = x_151;
x_110 = x_161;
x_111 = x_138;
x_112 = x_139;
x_113 = x_140;
x_114 = x_141;
x_115 = x_142;
x_116 = x_143;
x_117 = x_144;
x_118 = x_145;
x_119 = x_158;
goto block_133;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_162 = lean_ctor_get(x_156, 1);
lean_inc(x_162);
lean_dec(x_156);
x_163 = lean_ctor_get(x_148, 12);
lean_inc(x_163);
lean_dec(x_148);
x_164 = lean_ctor_get(x_163, 3);
lean_inc(x_164);
lean_dec(x_163);
x_165 = lean_ctor_get(x_164, 2);
lean_inc(x_165);
lean_dec(x_164);
x_166 = lean_ctor_get(x_157, 0);
lean_inc(x_166);
lean_dec(x_157);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_151);
x_167 = l_Lean_Meta_Grind_activateTheorem(x_166, x_151, x_138, x_139, x_140, x_141, x_142, x_143, x_144, x_145, x_162);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; 
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
lean_dec(x_167);
x_107 = x_153;
x_108 = x_137;
x_109 = x_151;
x_110 = x_165;
x_111 = x_138;
x_112 = x_139;
x_113 = x_140;
x_114 = x_141;
x_115 = x_142;
x_116 = x_143;
x_117 = x_144;
x_118 = x_145;
x_119 = x_168;
goto block_133;
}
else
{
lean_dec(x_165);
lean_dec(x_153);
lean_dec(x_151);
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_1);
return x_167;
}
}
}
else
{
uint8_t x_169; 
lean_dec(x_153);
lean_dec(x_151);
lean_dec(x_148);
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_1);
x_169 = !lean_is_exclusive(x_156);
if (x_169 == 0)
{
return x_156;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_156, 0);
x_171 = lean_ctor_get(x_156, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_156);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
}
else
{
uint8_t x_217; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_217 = !lean_is_exclusive(x_134);
if (x_217 == 0)
{
return x_134;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_134, 0);
x_219 = lean_ctor_get(x_134, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_134);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
return x_220;
}
}
block_72:
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_st_ref_get(x_12, x_20);
lean_dec(x_12);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = lean_ctor_get(x_23, 12);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_25, 3);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_ctor_get(x_26, 2);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_nat_dec_eq(x_27, x_11);
lean_dec(x_11);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_1);
x_29 = lean_box(0);
lean_ctor_set(x_21, 0, x_29);
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_free_object(x_21);
x_30 = l_Lean_Meta_Grind_getConfig___redArg(x_14, x_24);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get_uint8(x_31, sizeof(void*)*7 + 10);
lean_dec(x_31);
if (x_32 == 0)
{
uint8_t x_33; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_30, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set(x_30, 0, x_35);
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_30, 1);
lean_inc(x_39);
lean_dec(x_30);
x_40 = lean_mk_string_unchecked("failed to create E-match local theorem for", 42, 42);
x_41 = l_Lean_stringToMessageData(x_40);
lean_dec(x_40);
x_42 = l_Lean_indentExpr(x_1);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_mk_string_unchecked("", 0, 0);
x_45 = l_Lean_stringToMessageData(x_44);
lean_dec(x_44);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_Meta_Grind_reportIssue(x_46, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_39);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_48 = lean_ctor_get(x_21, 0);
x_49 = lean_ctor_get(x_21, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_21);
x_50 = lean_ctor_get(x_48, 12);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_ctor_get(x_50, 3);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_ctor_get(x_51, 2);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_nat_dec_eq(x_52, x_11);
lean_dec(x_11);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_1);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_49);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = l_Lean_Meta_Grind_getConfig___redArg(x_14, x_49);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get_uint8(x_57, sizeof(void*)*7 + 10);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_1);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_60 = x_56;
} else {
 lean_dec_ref(x_56);
 x_60 = lean_box(0);
}
x_61 = lean_box(0);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_63 = lean_ctor_get(x_56, 1);
lean_inc(x_63);
lean_dec(x_56);
x_64 = lean_mk_string_unchecked("failed to create E-match local theorem for", 42, 42);
x_65 = l_Lean_stringToMessageData(x_64);
lean_dec(x_64);
x_66 = l_Lean_indentExpr(x_1);
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_mk_string_unchecked("", 0, 0);
x_69 = l_Lean_stringToMessageData(x_68);
lean_dec(x_68);
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_Meta_Grind_reportIssue(x_70, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_63);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
return x_71;
}
}
}
}
block_106:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_86 = lean_st_ref_get(x_77, x_85);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_ctor_get(x_87, 12);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_ctor_get(x_89, 3);
lean_inc(x_90);
lean_dec(x_89);
x_91 = lean_ctor_get(x_90, 2);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_nat_dec_eq(x_91, x_76);
lean_dec(x_91);
if (x_92 == 0)
{
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
x_11 = x_76;
x_12 = x_77;
x_13 = x_78;
x_14 = x_79;
x_15 = x_80;
x_16 = x_81;
x_17 = x_82;
x_18 = x_83;
x_19 = x_84;
x_20 = x_88;
goto block_72;
}
else
{
lean_object* x_93; uint8_t x_94; lean_object* x_95; 
x_93 = lean_box(8);
x_94 = lean_unbox(x_93);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
x_95 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(x_74, x_73, x_94, x_81, x_82, x_83, x_84, x_88);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; 
lean_dec(x_75);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_11 = x_76;
x_12 = x_77;
x_13 = x_78;
x_14 = x_79;
x_15 = x_80;
x_16 = x_81;
x_17 = x_82;
x_18 = x_83;
x_19 = x_84;
x_20 = x_97;
goto block_72;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
lean_dec(x_95);
x_99 = lean_ctor_get(x_96, 0);
lean_inc(x_99);
lean_dec(x_96);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
x_100 = l_Lean_Meta_Grind_activateTheorem(x_99, x_75, x_77, x_78, x_79, x_80, x_81, x_82, x_83, x_84, x_98);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
x_11 = x_76;
x_12 = x_77;
x_13 = x_78;
x_14 = x_79;
x_15 = x_80;
x_16 = x_81;
x_17 = x_82;
x_18 = x_83;
x_19 = x_84;
x_20 = x_101;
goto block_72;
}
else
{
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_1);
return x_100;
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_95);
if (x_102 == 0)
{
return x_95;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_95, 0);
x_104 = lean_ctor_get(x_95, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_95);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
}
block_133:
{
lean_object* x_120; uint8_t x_121; lean_object* x_122; 
x_120 = lean_box(7);
x_121 = lean_unbox(x_120);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_107);
lean_inc(x_108);
x_122 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(x_108, x_107, x_121, x_115, x_116, x_117, x_118, x_119);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_73 = x_107;
x_74 = x_108;
x_75 = x_109;
x_76 = x_110;
x_77 = x_111;
x_78 = x_112;
x_79 = x_113;
x_80 = x_114;
x_81 = x_115;
x_82 = x_116;
x_83 = x_117;
x_84 = x_118;
x_85 = x_124;
goto block_106;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_122, 1);
lean_inc(x_125);
lean_dec(x_122);
x_126 = lean_ctor_get(x_123, 0);
lean_inc(x_126);
lean_dec(x_123);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_109);
x_127 = l_Lean_Meta_Grind_activateTheorem(x_126, x_109, x_111, x_112, x_113, x_114, x_115, x_116, x_117, x_118, x_125);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
lean_dec(x_127);
x_73 = x_107;
x_74 = x_108;
x_75 = x_109;
x_76 = x_110;
x_77 = x_111;
x_78 = x_112;
x_79 = x_113;
x_80 = x_114;
x_81 = x_115;
x_82 = x_116;
x_83 = x_117;
x_84 = x_118;
x_85 = x_128;
goto block_106;
}
else
{
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_1);
return x_127;
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_1);
x_129 = !lean_is_exclusive(x_122);
if (x_129 == 0)
{
return x_122;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_122, 0);
x_131 = lean_ctor_get(x_122, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_122);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropDown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_52; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_inc(x_1);
x_52 = l_Lean_Meta_Grind_isEqFalse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_11);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
lean_inc(x_1);
x_56 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_5, x_8, x_9, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_unbox(x_57);
lean_dec(x_57);
if (x_58 == 0)
{
uint8_t x_59; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_56);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_56, 0);
lean_dec(x_60);
x_61 = lean_box(0);
lean_ctor_set(x_56, 0, x_61);
return x_56;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_56, 1);
lean_inc(x_62);
lean_dec(x_56);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_56, 1);
lean_inc(x_65);
lean_dec(x_56);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_66 = l_Lean_Meta_Grind_eqResolution(x_1, x_6, x_7, x_8, x_9, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_Expr_hasLooseBVars(x_13);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_70 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_13, x_2, x_68);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_unbox(x_71);
lean_dec(x_71);
if (x_72 == 0)
{
uint8_t x_73; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_70);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_70, 0);
lean_dec(x_74);
x_75 = lean_box(0);
lean_ctor_set(x_70, 0, x_75);
return x_70;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_70, 1);
lean_inc(x_76);
lean_dec(x_70);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_70, 1);
lean_inc(x_79);
lean_dec(x_70);
lean_inc(x_13);
x_80 = l_Lean_Meta_Grind_isEqFalse(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_unbox(x_81);
lean_dec(x_81);
if (x_82 == 0)
{
x_15 = x_80;
goto block_51;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_12);
x_84 = l_Lean_Meta_isProp(x_12, x_6, x_7, x_8, x_9, x_83);
x_15 = x_84;
goto block_51;
}
}
else
{
x_15 = x_80;
goto block_51;
}
}
}
else
{
lean_object* x_85; 
lean_dec(x_13);
lean_dec(x_12);
x_85 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_68);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
lean_dec(x_13);
lean_dec(x_12);
x_86 = lean_ctor_get(x_67, 0);
lean_inc(x_86);
lean_dec(x_67);
x_87 = lean_ctor_get(x_66, 1);
lean_inc(x_87);
lean_dec(x_66);
x_88 = !lean_is_exclusive(x_86);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_89 = lean_ctor_get(x_86, 0);
x_90 = lean_ctor_get(x_86, 1);
x_114 = lean_mk_string_unchecked("grind", 5, 5);
x_115 = lean_mk_string_unchecked("eqResolution", 12, 12);
x_116 = l_Lean_Name_mkStr2(x_114, x_115);
lean_inc(x_116);
x_117 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_116, x_8, x_87);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_unbox(x_118);
lean_dec(x_118);
if (x_119 == 0)
{
lean_object* x_120; 
lean_dec(x_116);
lean_free_object(x_86);
x_120 = lean_ctor_get(x_117, 1);
lean_inc(x_120);
lean_dec(x_117);
x_91 = x_2;
x_92 = x_3;
x_93 = x_4;
x_94 = x_5;
x_95 = x_6;
x_96 = x_7;
x_97 = x_8;
x_98 = x_9;
x_99 = x_120;
goto block_113;
}
else
{
uint8_t x_121; 
x_121 = !lean_is_exclusive(x_117);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_117, 1);
x_123 = lean_ctor_get(x_117, 0);
lean_dec(x_123);
x_124 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_122);
if (lean_obj_tag(x_124) == 0)
{
uint8_t x_125; 
x_125 = !lean_is_exclusive(x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_126 = lean_ctor_get(x_124, 1);
x_127 = lean_ctor_get(x_124, 0);
lean_dec(x_127);
x_128 = lean_mk_string_unchecked("", 0, 0);
x_129 = l_Lean_stringToMessageData(x_128);
lean_dec(x_128);
lean_inc(x_1);
x_130 = l_Lean_MessageData_ofExpr(x_1);
lean_inc(x_129);
lean_ctor_set_tag(x_124, 7);
lean_ctor_set(x_124, 1, x_130);
lean_ctor_set(x_124, 0, x_129);
x_131 = lean_mk_string_unchecked(", ", 2, 2);
x_132 = l_Lean_stringToMessageData(x_131);
lean_dec(x_131);
lean_ctor_set_tag(x_117, 7);
lean_ctor_set(x_117, 1, x_132);
lean_ctor_set(x_117, 0, x_124);
lean_inc(x_89);
x_133 = l_Lean_MessageData_ofExpr(x_89);
lean_ctor_set_tag(x_86, 7);
lean_ctor_set(x_86, 1, x_133);
lean_ctor_set(x_86, 0, x_117);
x_134 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_134, 0, x_86);
lean_ctor_set(x_134, 1, x_129);
x_135 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_116, x_134, x_6, x_7, x_8, x_9, x_126);
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
lean_dec(x_135);
x_91 = x_2;
x_92 = x_3;
x_93 = x_4;
x_94 = x_5;
x_95 = x_6;
x_96 = x_7;
x_97 = x_8;
x_98 = x_9;
x_99 = x_136;
goto block_113;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_137 = lean_ctor_get(x_124, 1);
lean_inc(x_137);
lean_dec(x_124);
x_138 = lean_mk_string_unchecked("", 0, 0);
x_139 = l_Lean_stringToMessageData(x_138);
lean_dec(x_138);
lean_inc(x_1);
x_140 = l_Lean_MessageData_ofExpr(x_1);
lean_inc(x_139);
x_141 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
x_142 = lean_mk_string_unchecked(", ", 2, 2);
x_143 = l_Lean_stringToMessageData(x_142);
lean_dec(x_142);
lean_ctor_set_tag(x_117, 7);
lean_ctor_set(x_117, 1, x_143);
lean_ctor_set(x_117, 0, x_141);
lean_inc(x_89);
x_144 = l_Lean_MessageData_ofExpr(x_89);
lean_ctor_set_tag(x_86, 7);
lean_ctor_set(x_86, 1, x_144);
lean_ctor_set(x_86, 0, x_117);
x_145 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_145, 0, x_86);
lean_ctor_set(x_145, 1, x_139);
x_146 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_116, x_145, x_6, x_7, x_8, x_9, x_137);
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
lean_dec(x_146);
x_91 = x_2;
x_92 = x_3;
x_93 = x_4;
x_94 = x_5;
x_95 = x_6;
x_96 = x_7;
x_97 = x_8;
x_98 = x_9;
x_99 = x_147;
goto block_113;
}
}
else
{
lean_free_object(x_117);
lean_dec(x_116);
lean_free_object(x_86);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_124;
}
}
else
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_117, 1);
lean_inc(x_148);
lean_dec(x_117);
x_149 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_148);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_151 = x_149;
} else {
 lean_dec_ref(x_149);
 x_151 = lean_box(0);
}
x_152 = lean_mk_string_unchecked("", 0, 0);
x_153 = l_Lean_stringToMessageData(x_152);
lean_dec(x_152);
lean_inc(x_1);
x_154 = l_Lean_MessageData_ofExpr(x_1);
lean_inc(x_153);
if (lean_is_scalar(x_151)) {
 x_155 = lean_alloc_ctor(7, 2, 0);
} else {
 x_155 = x_151;
 lean_ctor_set_tag(x_155, 7);
}
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
x_156 = lean_mk_string_unchecked(", ", 2, 2);
x_157 = l_Lean_stringToMessageData(x_156);
lean_dec(x_156);
x_158 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_157);
lean_inc(x_89);
x_159 = l_Lean_MessageData_ofExpr(x_89);
lean_ctor_set_tag(x_86, 7);
lean_ctor_set(x_86, 1, x_159);
lean_ctor_set(x_86, 0, x_158);
x_160 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_160, 0, x_86);
lean_ctor_set(x_160, 1, x_153);
x_161 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_116, x_160, x_6, x_7, x_8, x_9, x_150);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
lean_dec(x_161);
x_91 = x_2;
x_92 = x_3;
x_93 = x_4;
x_94 = x_5;
x_95 = x_6;
x_96 = x_7;
x_97 = x_8;
x_98 = x_9;
x_99 = x_162;
goto block_113;
}
else
{
lean_dec(x_116);
lean_free_object(x_86);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_149;
}
}
}
block_113:
{
lean_object* x_100; 
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_1);
x_100 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_91, x_92, x_93, x_94, x_95, x_96, x_97, x_98, x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_91, x_102);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = l_Lean_Meta_mkOfEqTrueCore(x_1, x_101);
x_107 = l_Lean_Expr_app___override(x_90, x_106);
x_108 = l_Lean_Meta_Grind_addNewRawFact(x_107, x_89, x_104, x_91, x_92, x_93, x_94, x_95, x_96, x_97, x_98, x_105);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
return x_108;
}
else
{
uint8_t x_109; 
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_100);
if (x_109 == 0)
{
return x_100;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_100, 0);
x_111 = lean_ctor_get(x_100, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_100);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; 
x_163 = lean_ctor_get(x_86, 0);
x_164 = lean_ctor_get(x_86, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_86);
x_188 = lean_mk_string_unchecked("grind", 5, 5);
x_189 = lean_mk_string_unchecked("eqResolution", 12, 12);
x_190 = l_Lean_Name_mkStr2(x_188, x_189);
lean_inc(x_190);
x_191 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_190, x_8, x_87);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_unbox(x_192);
lean_dec(x_192);
if (x_193 == 0)
{
lean_object* x_194; 
lean_dec(x_190);
x_194 = lean_ctor_get(x_191, 1);
lean_inc(x_194);
lean_dec(x_191);
x_165 = x_2;
x_166 = x_3;
x_167 = x_4;
x_168 = x_5;
x_169 = x_6;
x_170 = x_7;
x_171 = x_8;
x_172 = x_9;
x_173 = x_194;
goto block_187;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_191, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_196 = x_191;
} else {
 lean_dec_ref(x_191);
 x_196 = lean_box(0);
}
x_197 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_195);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_198 = lean_ctor_get(x_197, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_199 = x_197;
} else {
 lean_dec_ref(x_197);
 x_199 = lean_box(0);
}
x_200 = lean_mk_string_unchecked("", 0, 0);
x_201 = l_Lean_stringToMessageData(x_200);
lean_dec(x_200);
lean_inc(x_1);
x_202 = l_Lean_MessageData_ofExpr(x_1);
lean_inc(x_201);
if (lean_is_scalar(x_199)) {
 x_203 = lean_alloc_ctor(7, 2, 0);
} else {
 x_203 = x_199;
 lean_ctor_set_tag(x_203, 7);
}
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
x_204 = lean_mk_string_unchecked(", ", 2, 2);
x_205 = l_Lean_stringToMessageData(x_204);
lean_dec(x_204);
if (lean_is_scalar(x_196)) {
 x_206 = lean_alloc_ctor(7, 2, 0);
} else {
 x_206 = x_196;
 lean_ctor_set_tag(x_206, 7);
}
lean_ctor_set(x_206, 0, x_203);
lean_ctor_set(x_206, 1, x_205);
lean_inc(x_163);
x_207 = l_Lean_MessageData_ofExpr(x_163);
x_208 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
x_209 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_201);
x_210 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_190, x_209, x_6, x_7, x_8, x_9, x_198);
x_211 = lean_ctor_get(x_210, 1);
lean_inc(x_211);
lean_dec(x_210);
x_165 = x_2;
x_166 = x_3;
x_167 = x_4;
x_168 = x_5;
x_169 = x_6;
x_170 = x_7;
x_171 = x_8;
x_172 = x_9;
x_173 = x_211;
goto block_187;
}
else
{
lean_dec(x_196);
lean_dec(x_190);
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_197;
}
}
block_187:
{
lean_object* x_174; 
lean_inc(x_172);
lean_inc(x_171);
lean_inc(x_170);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_166);
lean_inc(x_165);
lean_inc(x_1);
x_174 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_165, x_166, x_167, x_168, x_169, x_170, x_171, x_172, x_173);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec(x_174);
x_177 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_165, x_176);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = l_Lean_Meta_mkOfEqTrueCore(x_1, x_175);
x_181 = l_Lean_Expr_app___override(x_164, x_180);
x_182 = l_Lean_Meta_Grind_addNewRawFact(x_181, x_163, x_178, x_165, x_166, x_167, x_168, x_169, x_170, x_171, x_172, x_179);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_165);
return x_182;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_1);
x_183 = lean_ctor_get(x_174, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_174, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_185 = x_174;
} else {
 lean_dec_ref(x_174);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 2, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_183);
lean_ctor_set(x_186, 1, x_184);
return x_186;
}
}
}
}
}
else
{
uint8_t x_212; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_212 = !lean_is_exclusive(x_66);
if (x_212 == 0)
{
return x_66;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_66, 0);
x_214 = lean_ctor_get(x_66, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_66);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
}
}
else
{
uint8_t x_216; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_216 = !lean_is_exclusive(x_56);
if (x_216 == 0)
{
return x_56;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_56, 0);
x_218 = lean_ctor_get(x_56, 1);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_56);
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
return x_219;
}
}
}
else
{
lean_object* x_220; lean_object* x_221; 
x_220 = lean_ctor_get(x_52, 1);
lean_inc(x_220);
lean_dec(x_52);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_12);
x_221 = l_Lean_Meta_isProp(x_12, x_6, x_7, x_8, x_9, x_220);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; uint8_t x_271; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
x_271 = l_Lean_Expr_hasLooseBVars(x_13);
if (x_271 == 0)
{
uint8_t x_272; 
x_272 = lean_unbox(x_222);
lean_dec(x_222);
if (x_272 == 0)
{
goto block_270;
}
else
{
if (x_271 == 0)
{
lean_object* x_273; 
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_273 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_223);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
lean_dec(x_273);
x_276 = lean_mk_string_unchecked("Lean", 4, 4);
x_277 = lean_mk_string_unchecked("Grind", 5, 5);
x_278 = lean_mk_string_unchecked("eq_true_of_imp_eq_false", 23, 23);
lean_inc(x_277);
lean_inc(x_276);
x_279 = l_Lean_Name_mkStr3(x_276, x_277, x_278);
x_280 = lean_box(0);
x_281 = l_Lean_Expr_const___override(x_279, x_280);
lean_inc(x_274);
lean_inc(x_13);
lean_inc(x_12);
x_282 = l_Lean_mkApp3(x_281, x_12, x_13, x_274);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_12);
x_283 = l_Lean_Meta_Grind_pushEqTrue(x_12, x_282, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_275);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_284 = lean_ctor_get(x_283, 1);
lean_inc(x_284);
lean_dec(x_283);
x_285 = lean_mk_string_unchecked("eq_false_of_imp_eq_false", 24, 24);
x_286 = l_Lean_Name_mkStr3(x_276, x_277, x_285);
x_287 = l_Lean_Expr_const___override(x_286, x_280);
lean_inc(x_13);
x_288 = l_Lean_mkApp3(x_287, x_12, x_13, x_274);
x_289 = l_Lean_Meta_Grind_pushEqFalse(x_13, x_288, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_284);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_289;
}
else
{
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_274);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_283;
}
}
else
{
uint8_t x_290; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_290 = !lean_is_exclusive(x_273);
if (x_290 == 0)
{
return x_273;
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_291 = lean_ctor_get(x_273, 0);
x_292 = lean_ctor_get(x_273, 1);
lean_inc(x_292);
lean_inc(x_291);
lean_dec(x_273);
x_293 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_293, 0, x_291);
lean_ctor_set(x_293, 1, x_292);
return x_293;
}
}
}
else
{
goto block_270;
}
}
}
else
{
lean_dec(x_222);
goto block_270;
}
block_270:
{
lean_object* x_224; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_12);
x_224 = l_Lean_Meta_getLevel(x_12, x_6, x_7, x_8, x_9, x_223);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
lean_dec(x_224);
x_227 = lean_mk_string_unchecked("Exists", 6, 6);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_228 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_226);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
lean_dec(x_228);
x_231 = lean_box(0);
x_232 = lean_mk_string_unchecked("Lean", 4, 4);
x_233 = lean_mk_string_unchecked("Grind", 5, 5);
x_234 = lean_mk_string_unchecked("of_forall_eq_false", 18, 18);
x_235 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2, x_230);
lean_dec(x_1);
x_236 = !lean_is_exclusive(x_235);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_237 = lean_ctor_get(x_235, 0);
x_238 = lean_ctor_get(x_235, 1);
x_239 = l_Lean_Name_mkStr1(x_227);
lean_inc(x_13);
x_240 = l_Lean_mkNot(x_13);
lean_ctor_set_tag(x_235, 1);
lean_ctor_set(x_235, 1, x_231);
lean_ctor_set(x_235, 0, x_225);
x_241 = l_Lean_Name_mkStr3(x_232, x_233, x_234);
lean_inc(x_235);
x_242 = l_Lean_Expr_const___override(x_239, x_235);
lean_inc(x_12);
lean_inc(x_11);
x_243 = l_Lean_Expr_lam___override(x_11, x_12, x_240, x_14);
x_244 = l_Lean_Expr_const___override(x_241, x_235);
lean_inc(x_12);
x_245 = l_Lean_Expr_lam___override(x_11, x_12, x_13, x_14);
lean_inc(x_12);
x_246 = l_Lean_mkAppB(x_242, x_12, x_243);
x_247 = l_Lean_mkApp3(x_244, x_12, x_245, x_229);
x_248 = l_Lean_Meta_Grind_addNewRawFact(x_247, x_246, x_237, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_238);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_248;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_249 = lean_ctor_get(x_235, 0);
x_250 = lean_ctor_get(x_235, 1);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_235);
x_251 = l_Lean_Name_mkStr1(x_227);
lean_inc(x_13);
x_252 = l_Lean_mkNot(x_13);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_225);
lean_ctor_set(x_253, 1, x_231);
x_254 = l_Lean_Name_mkStr3(x_232, x_233, x_234);
lean_inc(x_253);
x_255 = l_Lean_Expr_const___override(x_251, x_253);
lean_inc(x_12);
lean_inc(x_11);
x_256 = l_Lean_Expr_lam___override(x_11, x_12, x_252, x_14);
x_257 = l_Lean_Expr_const___override(x_254, x_253);
lean_inc(x_12);
x_258 = l_Lean_Expr_lam___override(x_11, x_12, x_13, x_14);
lean_inc(x_12);
x_259 = l_Lean_mkAppB(x_255, x_12, x_256);
x_260 = l_Lean_mkApp3(x_257, x_12, x_258, x_229);
x_261 = l_Lean_Meta_Grind_addNewRawFact(x_260, x_259, x_249, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_250);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_261;
}
}
else
{
uint8_t x_262; 
lean_dec(x_227);
lean_dec(x_225);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_262 = !lean_is_exclusive(x_228);
if (x_262 == 0)
{
return x_228;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_228, 0);
x_264 = lean_ctor_get(x_228, 1);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_228);
x_265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
return x_265;
}
}
}
else
{
uint8_t x_266; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_266 = !lean_is_exclusive(x_224);
if (x_266 == 0)
{
return x_224;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_224, 0);
x_268 = lean_ctor_get(x_224, 1);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_224);
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
return x_269;
}
}
}
}
else
{
uint8_t x_294; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_294 = !lean_is_exclusive(x_221);
if (x_294 == 0)
{
return x_221;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_295 = lean_ctor_get(x_221, 0);
x_296 = lean_ctor_get(x_221, 1);
lean_inc(x_296);
lean_inc(x_295);
lean_dec(x_221);
x_297 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_297, 0, x_295);
lean_ctor_set(x_297, 1, x_296);
return x_297;
}
}
}
}
else
{
uint8_t x_298; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_298 = !lean_is_exclusive(x_52);
if (x_298 == 0)
{
return x_52;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_299 = lean_ctor_get(x_52, 0);
x_300 = lean_ctor_get(x_52, 1);
lean_inc(x_300);
lean_inc(x_299);
lean_dec(x_52);
x_301 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set(x_301, 1, x_300);
return x_301;
}
}
block_51:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec(x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_25 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_13);
x_28 = l_Lean_Meta_Grind_mkEqFalseProof(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_mk_string_unchecked("Lean", 4, 4);
x_32 = lean_mk_string_unchecked("Grind", 5, 5);
x_33 = lean_mk_string_unchecked("eq_false_of_imp_eq_true", 23, 23);
x_34 = l_Lean_Name_mkStr3(x_31, x_32, x_33);
x_35 = lean_box(0);
x_36 = l_Lean_Expr_const___override(x_34, x_35);
lean_inc(x_12);
x_37 = l_Lean_mkApp4(x_36, x_12, x_13, x_26, x_29);
x_38 = l_Lean_Meta_Grind_pushEqFalse(x_12, x_37, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_30);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_28);
if (x_39 == 0)
{
return x_28;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_28, 0);
x_41 = lean_ctor_get(x_28, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_28);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_25);
if (x_43 == 0)
{
return x_25;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_25, 0);
x_45 = lean_ctor_get(x_25, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_25);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_15);
if (x_47 == 0)
{
return x_15;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_15, 0);
x_49 = lean_ctor_get(x_15, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_15);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
else
{
lean_object* x_302; lean_object* x_303; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_302 = lean_box(0);
x_303 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_10);
return x_303;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateExistsDown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; 
lean_inc(x_1);
x_15 = l_Lean_Meta_Grind_isEqFalse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec(x_15);
lean_inc(x_1);
x_25 = l_Lean_Expr_cleanupAnnotations(x_1);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_24;
goto block_14;
}
else
{
lean_object* x_27; uint8_t x_28; 
lean_inc(x_25);
x_27 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_28 = l_Lean_Expr_isApp(x_27);
if (x_28 == 0)
{
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_24;
goto block_14;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_inc(x_27);
x_29 = l_Lean_Expr_appFnCleanup___redArg(x_27);
x_30 = lean_mk_string_unchecked("Exists", 6, 6);
x_31 = l_Lean_Name_mkStr1(x_30);
x_32 = l_Lean_Expr_isConstOf(x_29, x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_24;
goto block_14;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_dec(x_25);
x_34 = lean_mk_string_unchecked("Not", 3, 3);
x_35 = l_Lean_Name_mkStr1(x_34);
x_36 = lean_box(0);
x_37 = lean_unsigned_to_nat(0u);
x_38 = l_Lean_Expr_bvar___override(x_37);
lean_inc(x_33);
x_39 = l_Lean_Expr_app___override(x_33, x_38);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_40 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_27, 1);
lean_inc(x_43);
lean_dec(x_27);
x_44 = lean_mk_string_unchecked("forall_not_of_not_exists", 24, 24);
x_45 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2, x_42);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Expr_const___override(x_35, x_36);
x_49 = l_Lean_Expr_headBeta(x_39);
x_50 = lean_mk_string_unchecked("x", 1, 1);
x_51 = l_Lean_Expr_constLevels_x21(x_29);
lean_dec(x_29);
x_52 = l_Lean_Name_mkStr1(x_44);
x_53 = l_Lean_Expr_app___override(x_48, x_49);
x_54 = l_Lean_Name_mkStr1(x_50);
x_55 = lean_box(0);
x_56 = l_Lean_Expr_const___override(x_52, x_51);
x_57 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_41);
x_58 = lean_unbox(x_55);
lean_inc(x_43);
x_59 = l_Lean_Expr_forallE___override(x_54, x_43, x_53, x_58);
x_60 = l_Lean_mkApp3(x_56, x_43, x_33, x_57);
x_61 = l_Lean_Meta_Grind_addNewRawFact(x_60, x_59, x_46, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_47);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_61;
}
else
{
uint8_t x_62; 
lean_dec(x_39);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_40);
if (x_62 == 0)
{
return x_40;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_40, 0);
x_64 = lean_ctor_get(x_40, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_40);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_15);
if (x_66 == 0)
{
return x_15;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_15, 0);
x_68 = lean_ctor_get(x_15, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_15);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1____x40_Lean_Meta_Tactic_Grind_ForallProp___hyg_2854_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_mk_string_unchecked("Exists", 6, 6);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateExistsDown), 10, 0);
x_5 = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init_Grind_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Internalize(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_EqResolution(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_ForallProp(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Internalize(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_EqResolution(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1____x40_Lean_Meta_Tactic_Grind_ForallProp___hyg_2854_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
