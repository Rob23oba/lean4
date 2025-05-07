// Lean compiler output
// Module: Lean.Util.TestExtern
// Imports: Lean.Elab.SyntheticMVars Lean.Elab.Command Lean.Meta.Tactic.Unfold Lean.Meta.Eval Lean.Compiler.ImplementedByAttr
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
LEAN_EXPORT lean_object* l_elabTestExtern___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Meta_unfold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Meta_evalExpr(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l_elabTestExtern___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_implemented_by(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_isExtern(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_elabTestExtern___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Elab_Term_elabTermAndSynthesize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_testExternCmd;
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_elabTestExtern(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_elabTestExtern___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_testExternCmd() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_1 = lean_mk_string_unchecked("testExternCmd", 13, 13);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_unsigned_to_nat(1022u);
x_4 = lean_mk_string_unchecked("andthen", 7, 7);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_mk_string_unchecked("test_extern ", 12, 12);
x_7 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_mk_string_unchecked("term", 4, 4);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_11);
x_13 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_3);
lean_ctor_set(x_13, 2, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_elabTestExtern___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_mk_string_unchecked("test_extern: expects a function application", 43, 43);
x_10 = l_Lean_stringToMessageData(x_9);
lean_dec(x_9);
x_11 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_elabTestExtern___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_11 = l_Lean_Elab_Term_elabTermAndSynthesize(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Expr_getAppFn(x_12);
switch (lean_obj_tag(x_14)) {
case 0:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Expr_bvar___override(x_15);
x_17 = lean_apply_8(x_3, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_17;
}
case 1:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = l_Lean_Expr_fvar___override(x_18);
x_20 = lean_apply_8(x_3, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_20;
}
case 2:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_12);
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
x_22 = l_Lean_Expr_mvar___override(x_21);
x_23 = lean_apply_8(x_3, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_23;
}
case 3:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_12);
x_24 = lean_ctor_get(x_14, 0);
lean_inc(x_24);
lean_dec(x_14);
x_25 = l_Lean_Expr_sort___override(x_24);
x_26 = lean_apply_8(x_3, x_25, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_26;
}
case 4:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_97; uint8_t x_98; 
lean_dec(x_3);
x_27 = lean_ctor_get(x_14, 0);
lean_inc(x_27);
lean_dec(x_14);
x_28 = lean_st_ref_get(x_9, x_13);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_31 = x_28;
} else {
 lean_dec_ref(x_28);
 x_31 = lean_box(0);
}
x_97 = lean_ctor_get(x_29, 0);
lean_inc(x_97);
lean_dec(x_29);
lean_inc(x_27);
lean_inc(x_97);
x_98 = l_Lean_isExtern(x_97, x_27);
if (x_98 == 0)
{
lean_object* x_99; 
lean_inc(x_27);
x_99 = lean_get_implemented_by(x_97, x_27);
if (lean_obj_tag(x_99) == 0)
{
if (x_98 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_31);
lean_dec(x_12);
x_100 = lean_mk_string_unchecked("test_extern: ", 13, 13);
x_101 = l_Lean_stringToMessageData(x_100);
lean_dec(x_100);
x_102 = l_Lean_MessageData_ofName(x_27);
x_103 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_mk_string_unchecked(" does not have an @[extern] attribute or @[implemented_by] attribute", 68, 68);
x_105 = l_Lean_stringToMessageData(x_104);
lean_dec(x_104);
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_106, x_4, x_5, x_6, x_7, x_8, x_9, x_30);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_107;
}
else
{
goto block_96;
}
}
else
{
lean_dec(x_99);
goto block_96;
}
}
else
{
lean_dec(x_97);
goto block_96;
}
block_96:
{
lean_object* x_32; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_12);
x_32 = l_Lean_Meta_unfold(x_12, x_27, x_6, x_7, x_8, x_9, x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_35);
lean_inc(x_12);
x_36 = l_Lean_Meta_mkEq(x_12, x_35, x_6, x_7, x_8, x_9, x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_39 = l_Lean_Meta_mkDecide(x_37, x_6, x_7, x_8, x_9, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_mk_string_unchecked("Lean", 4, 4);
x_43 = lean_mk_string_unchecked("reduceBool", 10, 10);
x_44 = l_Lean_Name_mkStr2(x_42, x_43);
x_45 = lean_box(0);
x_46 = l_Lean_Expr_const___override(x_44, x_45);
x_47 = l_Lean_Expr_app___override(x_46, x_40);
x_48 = lean_mk_string_unchecked("Bool", 4, 4);
x_49 = l_Lean_Name_mkStr1(x_48);
x_50 = l_Lean_Expr_const___override(x_49, x_45);
x_51 = lean_box(1);
x_52 = lean_unbox(x_51);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_53 = l_Lean_Meta_evalExpr(lean_box(0), x_50, x_47, x_52, x_6, x_7, x_8, x_9, x_41);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_mk_string_unchecked("native implementation did not agree with reference implementation!\n", 67, 67);
x_58 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = l_Lean_MessageData_ofFormat(x_58);
x_60 = lean_mk_string_unchecked("Compare the outputs of:\n#eval ", 30, 30);
x_61 = l_Lean_stringToMessageData(x_60);
lean_dec(x_60);
x_62 = l_Lean_MessageData_ofExpr(x_12);
if (lean_is_scalar(x_31)) {
 x_63 = lean_alloc_ctor(7, 2, 0);
} else {
 x_63 = x_31;
 lean_ctor_set_tag(x_63, 7);
}
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_mk_string_unchecked("\n and\n#eval ", 12, 12);
x_65 = l_Lean_stringToMessageData(x_64);
lean_dec(x_64);
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_MessageData_ofExpr(x_35);
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_mk_string_unchecked("", 0, 0);
x_70 = l_Lean_stringToMessageData(x_69);
lean_dec(x_69);
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_59);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_72, x_4, x_5, x_6, x_7, x_8, x_9, x_56);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_73;
}
else
{
uint8_t x_74; 
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_74 = !lean_is_exclusive(x_53);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_53, 0);
lean_dec(x_75);
x_76 = lean_box(0);
lean_ctor_set(x_53, 0, x_76);
return x_53;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_53, 1);
lean_inc(x_77);
lean_dec(x_53);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_80 = !lean_is_exclusive(x_53);
if (x_80 == 0)
{
return x_53;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_53, 0);
x_82 = lean_ctor_get(x_53, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_53);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_84 = !lean_is_exclusive(x_39);
if (x_84 == 0)
{
return x_39;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_39, 0);
x_86 = lean_ctor_get(x_39, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_39);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_88 = !lean_is_exclusive(x_36);
if (x_88 == 0)
{
return x_36;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_36, 0);
x_90 = lean_ctor_get(x_36, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_36);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_31);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_92 = !lean_is_exclusive(x_32);
if (x_92 == 0)
{
return x_32;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_32, 0);
x_94 = lean_ctor_get(x_32, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_32);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
case 5:
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_12);
x_108 = lean_ctor_get(x_14, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_14, 1);
lean_inc(x_109);
lean_dec(x_14);
x_110 = l_Lean_Expr_app___override(x_108, x_109);
x_111 = lean_apply_8(x_3, x_110, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_111;
}
case 6:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_12);
x_112 = lean_ctor_get(x_14, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_14, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_14, 2);
lean_inc(x_114);
x_115 = lean_ctor_get_uint8(x_14, sizeof(void*)*3 + 8);
lean_dec(x_14);
x_116 = l_Lean_Expr_lam___override(x_112, x_113, x_114, x_115);
x_117 = lean_apply_8(x_3, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_117;
}
case 7:
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_12);
x_118 = lean_ctor_get(x_14, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_14, 1);
lean_inc(x_119);
x_120 = lean_ctor_get(x_14, 2);
lean_inc(x_120);
x_121 = lean_ctor_get_uint8(x_14, sizeof(void*)*3 + 8);
lean_dec(x_14);
x_122 = l_Lean_Expr_forallE___override(x_118, x_119, x_120, x_121);
x_123 = lean_apply_8(x_3, x_122, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_123;
}
case 8:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_12);
x_124 = lean_ctor_get(x_14, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_14, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_14, 2);
lean_inc(x_126);
x_127 = lean_ctor_get(x_14, 3);
lean_inc(x_127);
x_128 = lean_ctor_get_uint8(x_14, sizeof(void*)*4 + 8);
lean_dec(x_14);
x_129 = l_Lean_Expr_letE___override(x_124, x_125, x_126, x_127, x_128);
x_130 = lean_apply_8(x_3, x_129, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_130;
}
case 9:
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_12);
x_131 = lean_ctor_get(x_14, 0);
lean_inc(x_131);
lean_dec(x_14);
x_132 = l_Lean_Expr_lit___override(x_131);
x_133 = lean_apply_8(x_3, x_132, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_133;
}
case 10:
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_12);
x_134 = lean_ctor_get(x_14, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_14, 1);
lean_inc(x_135);
lean_dec(x_14);
x_136 = l_Lean_Expr_mdata___override(x_134, x_135);
x_137 = lean_apply_8(x_3, x_136, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_137;
}
default: 
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_12);
x_138 = lean_ctor_get(x_14, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_14, 1);
lean_inc(x_139);
x_140 = lean_ctor_get(x_14, 2);
lean_inc(x_140);
lean_dec(x_14);
x_141 = l_Lean_Expr_proj___override(x_138, x_139, x_140);
x_142 = lean_apply_8(x_3, x_141, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_142;
}
}
}
else
{
uint8_t x_143; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_143 = !lean_is_exclusive(x_11);
if (x_143 == 0)
{
return x_11;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_11, 0);
x_145 = lean_ctor_get(x_11, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_11);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
}
LEAN_EXPORT lean_object* l_elabTestExtern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_mk_string_unchecked("testExternCmd", 13, 13);
x_6 = l_Lean_Name_mkStr1(x_5);
lean_inc(x_1);
x_7 = l_Lean_Syntax_isOfKind(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_alloc_closure((void*)(l_elabTestExtern___lam__0___boxed), 8, 0);
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_closure((void*)(l_elabTestExtern___lam__1), 10, 3);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
lean_closure_set(x_13, 2, x_9);
x_14 = l_Lean_Elab_Command_liftTermElabM___redArg(x_13, x_2, x_3, x_4);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_elabTestExtern___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_elabTestExtern___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_elabTestExtern___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_elabTestExtern(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* initialize_Lean_Elab_SyntheticMVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Unfold(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Eval(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_ImplementedByAttr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_TestExtern(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_SyntheticMVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Unfold(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Eval(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ImplementedByAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_testExternCmd = _init_l_testExternCmd();
lean_mark_persistent(l_testExternCmd);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
