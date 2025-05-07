// Lean compiler output
// Module: Lean.Meta.Tactic.Refl
// Imports: Lean.Meta.Reduce Lean.Meta.Tactic.Util Lean.Meta.Tactic.Apply
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
LEAN_EXPORT lean_object* l_Lean_MVarId_heqOfEq___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_eqOfHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_observing_x3f___at___Lean_MVarId_iffOfEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_hrefl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_refl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_heqOfEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_heqOfEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_hrefl___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_refl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_hrefl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_eqOfHEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_eqOfHEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_heqOfEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_refl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_hrefl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_eqOfHEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_heqOfEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_hrefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_refl___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_1);
x_9 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_13 = l_Lean_MVarId_getType_x27(x_1, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_mk_string_unchecked("Eq", 2, 2);
lean_inc(x_16);
x_17 = l_Lean_Name_mkStr1(x_16);
x_18 = lean_unsigned_to_nat(3u);
x_19 = l_Lean_Expr_isAppOfArity(x_14, x_17, x_18);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_16);
lean_dec(x_3);
x_20 = lean_mk_string_unchecked("rfl", 3, 3);
x_21 = l_Lean_Name_mkStr1(x_20);
x_22 = lean_mk_string_unchecked("equality expected", 17, 17);
x_23 = l_Lean_stringToMessageData(x_22);
lean_dec(x_22);
x_24 = l_Lean_indentExpr(x_14);
lean_ctor_set_tag(x_9, 7);
lean_ctor_set(x_9, 1, x_24);
lean_ctor_set(x_9, 0, x_23);
x_25 = lean_mk_string_unchecked("", 0, 0);
x_26 = l_Lean_stringToMessageData(x_25);
lean_dec(x_25);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_9);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lean_Meta_throwTacticEx___redArg(x_21, x_1, x_28, x_4, x_5, x_6, x_7, x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = l_Lean_Expr_appFn_x21(x_14);
x_31 = l_Lean_Expr_appArg_x21(x_30);
x_32 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_31, x_5, x_15);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
x_36 = l_Lean_Expr_appArg_x21(x_14);
x_37 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_36, x_5, x_35);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_39);
lean_inc(x_34);
x_41 = l_Lean_Meta_isExprDefEq(x_34, x_39, x_4, x_5, x_6, x_7, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_30);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_3);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_mk_string_unchecked("rfl", 3, 3);
x_46 = l_Lean_Name_mkStr1(x_45);
x_47 = lean_mk_string_unchecked("equality lhs", 12, 12);
x_48 = l_Lean_stringToMessageData(x_47);
lean_dec(x_47);
x_49 = l_Lean_indentExpr(x_34);
lean_ctor_set_tag(x_37, 7);
lean_ctor_set(x_37, 1, x_49);
lean_ctor_set(x_37, 0, x_48);
x_50 = lean_mk_string_unchecked("\nis not definitionally equal to rhs", 35, 35);
x_51 = l_Lean_stringToMessageData(x_50);
lean_dec(x_50);
lean_ctor_set_tag(x_32, 7);
lean_ctor_set(x_32, 1, x_51);
lean_ctor_set(x_32, 0, x_37);
x_52 = l_Lean_indentExpr(x_39);
lean_ctor_set_tag(x_9, 7);
lean_ctor_set(x_9, 1, x_52);
lean_ctor_set(x_9, 0, x_32);
x_53 = lean_mk_string_unchecked("", 0, 0);
x_54 = l_Lean_stringToMessageData(x_53);
lean_dec(x_53);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_9);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = l_Lean_Meta_throwTacticEx___redArg(x_46, x_1, x_56, x_4, x_5, x_6, x_7, x_44);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_free_object(x_37);
lean_dec(x_39);
lean_free_object(x_32);
lean_free_object(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_58 = lean_ctor_get(x_41, 1);
lean_inc(x_58);
lean_dec(x_41);
x_59 = l_Lean_Expr_getAppFn(x_14);
lean_dec(x_14);
x_60 = l_Lean_Expr_constLevels_x21(x_59);
lean_dec(x_59);
x_61 = l_Lean_Expr_appFn_x21(x_30);
lean_dec(x_30);
x_62 = l_Lean_Expr_appArg_x21(x_61);
lean_dec(x_61);
x_63 = l_Lean_Name_mkStr2(x_16, x_3);
x_64 = l_Lean_Expr_const___override(x_63, x_60);
x_65 = l_Lean_mkAppB(x_64, x_62, x_34);
x_66 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_65, x_5, x_58);
lean_dec(x_5);
return x_66;
}
}
else
{
uint8_t x_67; 
lean_free_object(x_37);
lean_dec(x_39);
lean_free_object(x_32);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_16);
lean_dec(x_14);
lean_free_object(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_41);
if (x_67 == 0)
{
return x_41;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_41, 0);
x_69 = lean_ctor_get(x_41, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_41);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_37, 0);
x_72 = lean_ctor_get(x_37, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_37);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_71);
lean_inc(x_34);
x_73 = l_Lean_Meta_isExprDefEq(x_34, x_71, x_4, x_5, x_6, x_7, x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_unbox(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_30);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_3);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
x_77 = lean_mk_string_unchecked("rfl", 3, 3);
x_78 = l_Lean_Name_mkStr1(x_77);
x_79 = lean_mk_string_unchecked("equality lhs", 12, 12);
x_80 = l_Lean_stringToMessageData(x_79);
lean_dec(x_79);
x_81 = l_Lean_indentExpr(x_34);
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_mk_string_unchecked("\nis not definitionally equal to rhs", 35, 35);
x_84 = l_Lean_stringToMessageData(x_83);
lean_dec(x_83);
lean_ctor_set_tag(x_32, 7);
lean_ctor_set(x_32, 1, x_84);
lean_ctor_set(x_32, 0, x_82);
x_85 = l_Lean_indentExpr(x_71);
lean_ctor_set_tag(x_9, 7);
lean_ctor_set(x_9, 1, x_85);
lean_ctor_set(x_9, 0, x_32);
x_86 = lean_mk_string_unchecked("", 0, 0);
x_87 = l_Lean_stringToMessageData(x_86);
lean_dec(x_86);
x_88 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_88, 0, x_9);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = l_Lean_Meta_throwTacticEx___redArg(x_78, x_1, x_89, x_4, x_5, x_6, x_7, x_76);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_71);
lean_free_object(x_32);
lean_free_object(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_91 = lean_ctor_get(x_73, 1);
lean_inc(x_91);
lean_dec(x_73);
x_92 = l_Lean_Expr_getAppFn(x_14);
lean_dec(x_14);
x_93 = l_Lean_Expr_constLevels_x21(x_92);
lean_dec(x_92);
x_94 = l_Lean_Expr_appFn_x21(x_30);
lean_dec(x_30);
x_95 = l_Lean_Expr_appArg_x21(x_94);
lean_dec(x_94);
x_96 = l_Lean_Name_mkStr2(x_16, x_3);
x_97 = l_Lean_Expr_const___override(x_96, x_93);
x_98 = l_Lean_mkAppB(x_97, x_95, x_34);
x_99 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_98, x_5, x_91);
lean_dec(x_5);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_71);
lean_free_object(x_32);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_16);
lean_dec(x_14);
lean_free_object(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_100 = lean_ctor_get(x_73, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_73, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_102 = x_73;
} else {
 lean_dec_ref(x_73);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_104 = lean_ctor_get(x_32, 0);
x_105 = lean_ctor_get(x_32, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_32);
x_106 = l_Lean_Expr_appArg_x21(x_14);
x_107 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_106, x_5, x_105);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_110 = x_107;
} else {
 lean_dec_ref(x_107);
 x_110 = lean_box(0);
}
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_108);
lean_inc(x_104);
x_111 = l_Lean_Meta_isExprDefEq(x_104, x_108, x_4, x_5, x_6, x_7, x_109);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; uint8_t x_113; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_unbox(x_112);
lean_dec(x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_30);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_3);
x_114 = lean_ctor_get(x_111, 1);
lean_inc(x_114);
lean_dec(x_111);
x_115 = lean_mk_string_unchecked("rfl", 3, 3);
x_116 = l_Lean_Name_mkStr1(x_115);
x_117 = lean_mk_string_unchecked("equality lhs", 12, 12);
x_118 = l_Lean_stringToMessageData(x_117);
lean_dec(x_117);
x_119 = l_Lean_indentExpr(x_104);
if (lean_is_scalar(x_110)) {
 x_120 = lean_alloc_ctor(7, 2, 0);
} else {
 x_120 = x_110;
 lean_ctor_set_tag(x_120, 7);
}
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_mk_string_unchecked("\nis not definitionally equal to rhs", 35, 35);
x_122 = l_Lean_stringToMessageData(x_121);
lean_dec(x_121);
x_123 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_122);
x_124 = l_Lean_indentExpr(x_108);
lean_ctor_set_tag(x_9, 7);
lean_ctor_set(x_9, 1, x_124);
lean_ctor_set(x_9, 0, x_123);
x_125 = lean_mk_string_unchecked("", 0, 0);
x_126 = l_Lean_stringToMessageData(x_125);
lean_dec(x_125);
x_127 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_127, 0, x_9);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_127);
x_129 = l_Lean_Meta_throwTacticEx___redArg(x_116, x_1, x_128, x_4, x_5, x_6, x_7, x_114);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_110);
lean_dec(x_108);
lean_free_object(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_130 = lean_ctor_get(x_111, 1);
lean_inc(x_130);
lean_dec(x_111);
x_131 = l_Lean_Expr_getAppFn(x_14);
lean_dec(x_14);
x_132 = l_Lean_Expr_constLevels_x21(x_131);
lean_dec(x_131);
x_133 = l_Lean_Expr_appFn_x21(x_30);
lean_dec(x_30);
x_134 = l_Lean_Expr_appArg_x21(x_133);
lean_dec(x_133);
x_135 = l_Lean_Name_mkStr2(x_16, x_3);
x_136 = l_Lean_Expr_const___override(x_135, x_132);
x_137 = l_Lean_mkAppB(x_136, x_134, x_104);
x_138 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_137, x_5, x_130);
lean_dec(x_5);
return x_138;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_110);
lean_dec(x_108);
lean_dec(x_104);
lean_dec(x_30);
lean_dec(x_16);
lean_dec(x_14);
lean_free_object(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_139 = lean_ctor_get(x_111, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_111, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_141 = x_111;
} else {
 lean_dec_ref(x_111);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
}
}
else
{
uint8_t x_143; 
lean_free_object(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_143 = !lean_is_exclusive(x_13);
if (x_143 == 0)
{
return x_13;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_13, 0);
x_145 = lean_ctor_get(x_13, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_13);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
else
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_9, 1);
lean_inc(x_147);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_148 = l_Lean_MVarId_getType_x27(x_1, x_4, x_5, x_6, x_7, x_147);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = lean_mk_string_unchecked("Eq", 2, 2);
lean_inc(x_151);
x_152 = l_Lean_Name_mkStr1(x_151);
x_153 = lean_unsigned_to_nat(3u);
x_154 = l_Lean_Expr_isAppOfArity(x_149, x_152, x_153);
lean_dec(x_152);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_151);
lean_dec(x_3);
x_155 = lean_mk_string_unchecked("rfl", 3, 3);
x_156 = l_Lean_Name_mkStr1(x_155);
x_157 = lean_mk_string_unchecked("equality expected", 17, 17);
x_158 = l_Lean_stringToMessageData(x_157);
lean_dec(x_157);
x_159 = l_Lean_indentExpr(x_149);
x_160 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_mk_string_unchecked("", 0, 0);
x_162 = l_Lean_stringToMessageData(x_161);
lean_dec(x_161);
x_163 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_163, 0, x_160);
lean_ctor_set(x_163, 1, x_162);
x_164 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_164, 0, x_163);
x_165 = l_Lean_Meta_throwTacticEx___redArg(x_156, x_1, x_164, x_4, x_5, x_6, x_7, x_150);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_165;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_166 = l_Lean_Expr_appFn_x21(x_149);
x_167 = l_Lean_Expr_appArg_x21(x_166);
x_168 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_167, x_5, x_150);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_171 = x_168;
} else {
 lean_dec_ref(x_168);
 x_171 = lean_box(0);
}
x_172 = l_Lean_Expr_appArg_x21(x_149);
x_173 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_172, x_5, x_170);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_176 = x_173;
} else {
 lean_dec_ref(x_173);
 x_176 = lean_box(0);
}
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_174);
lean_inc(x_169);
x_177 = l_Lean_Meta_isExprDefEq(x_169, x_174, x_4, x_5, x_6, x_7, x_175);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; uint8_t x_179; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_unbox(x_178);
lean_dec(x_178);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_166);
lean_dec(x_151);
lean_dec(x_149);
lean_dec(x_3);
x_180 = lean_ctor_get(x_177, 1);
lean_inc(x_180);
lean_dec(x_177);
x_181 = lean_mk_string_unchecked("rfl", 3, 3);
x_182 = l_Lean_Name_mkStr1(x_181);
x_183 = lean_mk_string_unchecked("equality lhs", 12, 12);
x_184 = l_Lean_stringToMessageData(x_183);
lean_dec(x_183);
x_185 = l_Lean_indentExpr(x_169);
if (lean_is_scalar(x_176)) {
 x_186 = lean_alloc_ctor(7, 2, 0);
} else {
 x_186 = x_176;
 lean_ctor_set_tag(x_186, 7);
}
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
x_187 = lean_mk_string_unchecked("\nis not definitionally equal to rhs", 35, 35);
x_188 = l_Lean_stringToMessageData(x_187);
lean_dec(x_187);
if (lean_is_scalar(x_171)) {
 x_189 = lean_alloc_ctor(7, 2, 0);
} else {
 x_189 = x_171;
 lean_ctor_set_tag(x_189, 7);
}
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_188);
x_190 = l_Lean_indentExpr(x_174);
x_191 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
x_192 = lean_mk_string_unchecked("", 0, 0);
x_193 = l_Lean_stringToMessageData(x_192);
lean_dec(x_192);
x_194 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_193);
x_195 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_195, 0, x_194);
x_196 = l_Lean_Meta_throwTacticEx___redArg(x_182, x_1, x_195, x_4, x_5, x_6, x_7, x_180);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_196;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_176);
lean_dec(x_174);
lean_dec(x_171);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_197 = lean_ctor_get(x_177, 1);
lean_inc(x_197);
lean_dec(x_177);
x_198 = l_Lean_Expr_getAppFn(x_149);
lean_dec(x_149);
x_199 = l_Lean_Expr_constLevels_x21(x_198);
lean_dec(x_198);
x_200 = l_Lean_Expr_appFn_x21(x_166);
lean_dec(x_166);
x_201 = l_Lean_Expr_appArg_x21(x_200);
lean_dec(x_200);
x_202 = l_Lean_Name_mkStr2(x_151, x_3);
x_203 = l_Lean_Expr_const___override(x_202, x_199);
x_204 = l_Lean_mkAppB(x_203, x_201, x_169);
x_205 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_204, x_5, x_197);
lean_dec(x_5);
return x_205;
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_176);
lean_dec(x_174);
lean_dec(x_171);
lean_dec(x_169);
lean_dec(x_166);
lean_dec(x_151);
lean_dec(x_149);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_206 = lean_ctor_get(x_177, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_177, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_208 = x_177;
} else {
 lean_dec_ref(x_177);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(1, 2, 0);
} else {
 x_209 = x_208;
}
lean_ctor_set(x_209, 0, x_206);
lean_ctor_set(x_209, 1, x_207);
return x_209;
}
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_210 = lean_ctor_get(x_148, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_148, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_212 = x_148;
} else {
 lean_dec_ref(x_148);
 x_212 = lean_box(0);
}
if (lean_is_scalar(x_212)) {
 x_213 = lean_alloc_ctor(1, 2, 0);
} else {
 x_213 = x_212;
}
lean_ctor_set(x_213, 0, x_210);
lean_ctor_set(x_213, 1, x_211);
return x_213;
}
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_refl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_mk_string_unchecked("refl", 4, 4);
lean_inc(x_7);
x_8 = l_Lean_Name_mkStr1(x_7);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_MVarId_refl___lam__0), 8, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_7);
x_10 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_refl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_refl(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_heqOfEq___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Meta_mkFreshLevelMVar(x_2, x_3, x_4, x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = lean_mk_string_unchecked("heq_of_eq", 9, 9);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_box(0);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_12);
x_13 = l_Lean_Expr_const___override(x_11, x_7);
x_14 = lean_box(0);
x_15 = lean_box(1);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 0, 4);
x_18 = lean_unbox(x_14);
lean_ctor_set_uint8(x_17, 0, x_18);
x_19 = lean_unbox(x_15);
lean_ctor_set_uint8(x_17, 1, x_19);
x_20 = lean_unbox(x_16);
lean_ctor_set_uint8(x_17, 2, x_20);
x_21 = lean_unbox(x_15);
lean_ctor_set_uint8(x_17, 3, x_21);
x_22 = l_Lean_MVarId_apply(x_1, x_13, x_17, x_2, x_3, x_4, x_5, x_9);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; 
x_23 = lean_ctor_get(x_7, 0);
x_24 = lean_ctor_get(x_7, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_7);
x_25 = lean_mk_string_unchecked("heq_of_eq", 9, 9);
x_26 = l_Lean_Name_mkStr1(x_25);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Expr_const___override(x_26, x_28);
x_30 = lean_box(0);
x_31 = lean_box(1);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 0, 4);
x_34 = lean_unbox(x_30);
lean_ctor_set_uint8(x_33, 0, x_34);
x_35 = lean_unbox(x_31);
lean_ctor_set_uint8(x_33, 1, x_35);
x_36 = lean_unbox(x_32);
lean_ctor_set_uint8(x_33, 2, x_36);
x_37 = lean_unbox(x_31);
lean_ctor_set_uint8(x_33, 3, x_37);
x_38 = l_Lean_MVarId_apply(x_1, x_29, x_33, x_2, x_3, x_4, x_5, x_24);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_heqOfEq___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_observing_x3f___at___Lean_MVarId_iffOfEq_spec__0(lean_box(0), x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
lean_ctor_set(x_8, 0, x_2);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_8, 0);
lean_dec(x_16);
lean_ctor_set(x_8, 0, x_2);
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_8);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_8, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
lean_ctor_set(x_8, 0, x_22);
return x_8;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_dec(x_8);
x_24 = lean_ctor_get(x_14, 0);
lean_inc(x_24);
lean_dec(x_14);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_19);
lean_dec(x_14);
x_26 = !lean_is_exclusive(x_8);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_8, 0);
lean_dec(x_27);
lean_ctor_set(x_8, 0, x_2);
return x_8;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_8, 1);
lean_inc(x_28);
lean_dec(x_8);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_8);
if (x_30 == 0)
{
return x_8;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_8, 0);
x_32 = lean_ctor_get(x_8, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_8);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_heqOfEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_MVarId_heqOfEq___lam__0___boxed), 6, 1);
lean_closure_set(x_7, 0, x_1);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_MVarId_heqOfEq___lam__1), 7, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_heqOfEq___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_heqOfEq___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_heqOfEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_heqOfEq(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_eqOfHEq___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Meta_mkFreshLevelMVar(x_2, x_3, x_4, x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = lean_mk_string_unchecked("eq_of_heq", 9, 9);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_box(0);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_12);
x_13 = l_Lean_Expr_const___override(x_11, x_7);
x_14 = lean_box(0);
x_15 = lean_box(1);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 0, 4);
x_18 = lean_unbox(x_14);
lean_ctor_set_uint8(x_17, 0, x_18);
x_19 = lean_unbox(x_15);
lean_ctor_set_uint8(x_17, 1, x_19);
x_20 = lean_unbox(x_16);
lean_ctor_set_uint8(x_17, 2, x_20);
x_21 = lean_unbox(x_15);
lean_ctor_set_uint8(x_17, 3, x_21);
x_22 = l_Lean_MVarId_apply(x_1, x_13, x_17, x_2, x_3, x_4, x_5, x_9);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; 
x_23 = lean_ctor_get(x_7, 0);
x_24 = lean_ctor_get(x_7, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_7);
x_25 = lean_mk_string_unchecked("eq_of_heq", 9, 9);
x_26 = l_Lean_Name_mkStr1(x_25);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Expr_const___override(x_26, x_28);
x_30 = lean_box(0);
x_31 = lean_box(1);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 0, 4);
x_34 = lean_unbox(x_30);
lean_ctor_set_uint8(x_33, 0, x_34);
x_35 = lean_unbox(x_31);
lean_ctor_set_uint8(x_33, 1, x_35);
x_36 = lean_unbox(x_32);
lean_ctor_set_uint8(x_33, 2, x_36);
x_37 = lean_unbox(x_31);
lean_ctor_set_uint8(x_33, 3, x_37);
x_38 = l_Lean_MVarId_apply(x_1, x_29, x_33, x_2, x_3, x_4, x_5, x_24);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_eqOfHEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_MVarId_eqOfHEq___lam__0___boxed), 6, 1);
lean_closure_set(x_7, 0, x_1);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_MVarId_heqOfEq___lam__1), 7, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_eqOfHEq___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_eqOfHEq___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_eqOfHEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_eqOfHEq(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_hrefl___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Meta_mkFreshLevelMVar(x_2, x_3, x_4, x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = lean_mk_string_unchecked("HEq", 3, 3);
x_11 = lean_mk_string_unchecked("refl", 4, 4);
x_12 = l_Lean_Name_mkStr2(x_10, x_11);
x_13 = lean_box(0);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_13);
x_14 = l_Lean_Expr_const___override(x_12, x_7);
x_15 = lean_box(0);
x_16 = lean_box(1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 0, 4);
x_19 = lean_unbox(x_15);
lean_ctor_set_uint8(x_18, 0, x_19);
x_20 = lean_unbox(x_16);
lean_ctor_set_uint8(x_18, 1, x_20);
x_21 = lean_unbox(x_17);
lean_ctor_set_uint8(x_18, 2, x_21);
x_22 = lean_unbox(x_16);
lean_ctor_set_uint8(x_18, 3, x_22);
x_23 = l_Lean_MVarId_apply(x_1, x_14, x_18, x_2, x_3, x_4, x_5, x_9);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; lean_object* x_40; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_7);
x_26 = lean_mk_string_unchecked("HEq", 3, 3);
x_27 = lean_mk_string_unchecked("refl", 4, 4);
x_28 = l_Lean_Name_mkStr2(x_26, x_27);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Expr_const___override(x_28, x_30);
x_32 = lean_box(0);
x_33 = lean_box(1);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 0, 4);
x_36 = lean_unbox(x_32);
lean_ctor_set_uint8(x_35, 0, x_36);
x_37 = lean_unbox(x_33);
lean_ctor_set_uint8(x_35, 1, x_37);
x_38 = lean_unbox(x_34);
lean_ctor_set_uint8(x_35, 2, x_38);
x_39 = lean_unbox(x_33);
lean_ctor_set_uint8(x_35, 3, x_39);
x_40 = l_Lean_MVarId_apply(x_1, x_31, x_35, x_2, x_3, x_4, x_5, x_25);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_hrefl___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_observing_x3f___at___Lean_MVarId_iffOfEq_spec__0(lean_box(0), x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
if (lean_obj_tag(x_10) == 0)
{
lean_free_object(x_8);
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_10, 0);
lean_inc(x_21);
lean_dec(x_10);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_box(0);
lean_ctor_set(x_8, 0, x_22);
return x_8;
}
else
{
lean_dec(x_21);
lean_free_object(x_8);
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
goto block_20;
}
}
block_20:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_mk_string_unchecked("hrefl", 5, 5);
x_17 = l_Lean_Name_mkStr1(x_16);
x_18 = lean_box(0);
x_19 = l_Lean_Meta_throwTacticEx___redArg(x_17, x_2, x_18, x_12, x_13, x_14, x_15, x_11);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
return x_19;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_8, 0);
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_8);
if (lean_obj_tag(x_23) == 0)
{
x_25 = x_3;
x_26 = x_4;
x_27 = x_5;
x_28 = x_6;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_23, 0);
lean_inc(x_34);
lean_dec(x_23);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_24);
return x_36;
}
else
{
lean_dec(x_34);
x_25 = x_3;
x_26 = x_4;
x_27 = x_5;
x_28 = x_6;
goto block_33;
}
}
block_33:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_mk_string_unchecked("hrefl", 5, 5);
x_30 = l_Lean_Name_mkStr1(x_29);
x_31 = lean_box(0);
x_32 = l_Lean_Meta_throwTacticEx___redArg(x_30, x_2, x_31, x_25, x_26, x_27, x_28, x_24);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
return x_32;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_8);
if (x_37 == 0)
{
return x_8;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_8, 0);
x_39 = lean_ctor_get(x_8, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_8);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_hrefl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_MVarId_hrefl___lam__0___boxed), 6, 1);
lean_closure_set(x_7, 0, x_1);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_MVarId_hrefl___lam__1), 7, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_hrefl___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_hrefl___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_hrefl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_hrefl(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* initialize_Lean_Meta_Reduce(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Refl(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Reduce(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
