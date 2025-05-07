// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Proj
// Imports: Lean.ProjFns Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.Internalize
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
lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Meta_Grind_propagateProjEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_Grind_pushEqCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getRoot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isCongrRoot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateProjEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Meta_Grind_propagateProjEq_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Meta_Grind_propagateProjEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Meta_Grind_propagateProjEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_shareCommon___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_get_projection_info(lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Meta_Grind_propagateProjEq_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_get_projection_info(x_7, x_1);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_get_projection_info(x_11, x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Meta_Grind_propagateProjEq_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_getProjectionFnInfo_x3f___at___Lean_Meta_Grind_propagateProjEq_spec__0___redArg(x_1, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateProjEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_11) == 4)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_getProjectionFnInfo_x3f___at___Lean_Meta_Grind_propagateProjEq_spec__0___redArg(x_12, x_9, x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_22 = lean_ctor_get(x_13, 1);
x_23 = lean_ctor_get(x_13, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_14, 0);
lean_inc(x_24);
lean_dec(x_14);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_25, x_26);
x_28 = l_Lean_Expr_getAppNumArgs(x_1);
x_29 = lean_nat_dec_eq(x_27, x_28);
lean_dec(x_28);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = lean_box(0);
lean_ctor_set(x_13, 0, x_30);
return x_13;
}
else
{
lean_object* x_31; 
lean_free_object(x_13);
lean_inc(x_1);
x_31 = l_Lean_Meta_Grind_isCongrRoot___redArg(x_1, x_2, x_8, x_9, x_22);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
uint8_t x_34; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_31, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_31, 0, x_36);
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
lean_dec(x_31);
x_41 = lean_st_ref_get(x_2, x_40);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
x_45 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_45);
x_46 = l_Lean_Meta_Grind_Goal_getRoot(x_43, x_45, x_8, x_9, x_44);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_129; uint8_t x_130; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_129 = lean_ctor_get(x_24, 0);
lean_inc(x_129);
x_130 = l_Lean_Expr_isAppOf(x_47, x_129);
lean_dec(x_129);
if (x_130 == 0)
{
lean_object* x_131; 
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_45);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_131 = lean_box(0);
lean_ctor_set(x_41, 1, x_48);
lean_ctor_set(x_41, 0, x_131);
return x_41;
}
else
{
size_t x_132; size_t x_133; uint8_t x_134; 
lean_free_object(x_41);
x_132 = lean_ptr_addr(x_45);
lean_dec(x_45);
x_133 = lean_ptr_addr(x_47);
x_134 = lean_usize_dec_eq(x_132, x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_135 = l_Lean_Expr_appFn_x21(x_1);
lean_inc(x_47);
x_136 = l_Lean_Expr_app___override(x_135, x_47);
x_137 = l_Lean_Meta_Grind_shareCommon___redArg(x_136, x_5, x_48);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_140 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2, x_139);
lean_dec(x_1);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_138);
x_144 = lean_grind_internalize(x_138, x_141, x_143, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_142);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; 
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
x_80 = x_138;
x_81 = x_2;
x_82 = x_3;
x_83 = x_4;
x_84 = x_5;
x_85 = x_6;
x_86 = x_7;
x_87 = x_8;
x_88 = x_9;
x_89 = x_145;
goto block_128;
}
else
{
lean_dec(x_138);
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_144;
}
}
else
{
x_80 = x_1;
x_81 = x_2;
x_82 = x_3;
x_83 = x_4;
x_84 = x_5;
x_85 = x_6;
x_86 = x_7;
x_87 = x_8;
x_88 = x_9;
x_89 = x_48;
goto block_128;
}
}
block_79:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_24, 2);
lean_inc(x_60);
lean_dec(x_24);
x_61 = lean_nat_add(x_25, x_60);
lean_dec(x_60);
lean_dec(x_25);
x_62 = l_Lean_Expr_getAppNumArgs(x_47);
x_63 = lean_nat_dec_lt(x_61, x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_47);
x_64 = lean_box(0);
if (lean_is_scalar(x_49)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_49;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_59);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_49);
x_66 = lean_nat_sub(x_62, x_61);
lean_dec(x_61);
lean_dec(x_62);
x_67 = lean_nat_sub(x_66, x_26);
lean_dec(x_66);
x_68 = l_Lean_Expr_getRevArg_x21(x_47, x_67);
lean_dec(x_47);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_68);
x_69 = l_Lean_Meta_mkEqRefl(x_68, x_55, x_56, x_57, x_58, x_59);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_box(0);
x_73 = lean_unbox(x_72);
x_74 = l_Lean_Meta_Grind_pushEqCore(x_50, x_68, x_70, x_73, x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_71);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
return x_74;
}
else
{
uint8_t x_75; 
lean_dec(x_68);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
x_75 = !lean_is_exclusive(x_69);
if (x_75 == 0)
{
return x_69;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_69, 0);
x_77 = lean_ctor_get(x_69, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_69);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
block_128:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_90 = lean_mk_string_unchecked("grind", 5, 5);
x_91 = lean_mk_string_unchecked("debug", 5, 5);
x_92 = lean_mk_string_unchecked("proj", 4, 4);
x_93 = l_Lean_Name_mkStr3(x_90, x_91, x_92);
lean_inc(x_93);
x_94 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_93, x_87, x_89);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_unbox(x_95);
lean_dec(x_95);
if (x_96 == 0)
{
lean_object* x_97; 
lean_dec(x_93);
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
lean_dec(x_94);
x_50 = x_80;
x_51 = x_81;
x_52 = x_82;
x_53 = x_83;
x_54 = x_84;
x_55 = x_85;
x_56 = x_86;
x_57 = x_87;
x_58 = x_88;
x_59 = x_97;
goto block_79;
}
else
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_94);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_94, 1);
x_100 = lean_ctor_get(x_94, 0);
lean_dec(x_100);
x_101 = l_Lean_Meta_Grind_updateLastTag(x_81, x_82, x_83, x_84, x_85, x_86, x_87, x_88, x_99);
if (lean_obj_tag(x_101) == 0)
{
uint8_t x_102; 
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_103 = lean_ctor_get(x_101, 1);
x_104 = lean_ctor_get(x_101, 0);
lean_dec(x_104);
x_105 = lean_mk_string_unchecked("", 0, 0);
x_106 = l_Lean_stringToMessageData(x_105);
lean_dec(x_105);
lean_inc(x_80);
x_107 = l_Lean_MessageData_ofExpr(x_80);
lean_inc(x_106);
lean_ctor_set_tag(x_101, 7);
lean_ctor_set(x_101, 1, x_107);
lean_ctor_set(x_101, 0, x_106);
lean_ctor_set_tag(x_94, 7);
lean_ctor_set(x_94, 1, x_106);
lean_ctor_set(x_94, 0, x_101);
x_108 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_93, x_94, x_85, x_86, x_87, x_88, x_103);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
x_50 = x_80;
x_51 = x_81;
x_52 = x_82;
x_53 = x_83;
x_54 = x_84;
x_55 = x_85;
x_56 = x_86;
x_57 = x_87;
x_58 = x_88;
x_59 = x_109;
goto block_79;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_110 = lean_ctor_get(x_101, 1);
lean_inc(x_110);
lean_dec(x_101);
x_111 = lean_mk_string_unchecked("", 0, 0);
x_112 = l_Lean_stringToMessageData(x_111);
lean_dec(x_111);
lean_inc(x_80);
x_113 = l_Lean_MessageData_ofExpr(x_80);
lean_inc(x_112);
x_114 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
lean_ctor_set_tag(x_94, 7);
lean_ctor_set(x_94, 1, x_112);
lean_ctor_set(x_94, 0, x_114);
x_115 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_93, x_94, x_85, x_86, x_87, x_88, x_110);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
lean_dec(x_115);
x_50 = x_80;
x_51 = x_81;
x_52 = x_82;
x_53 = x_83;
x_54 = x_84;
x_55 = x_85;
x_56 = x_86;
x_57 = x_87;
x_58 = x_88;
x_59 = x_116;
goto block_79;
}
}
else
{
lean_free_object(x_94);
lean_dec(x_93);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_25);
lean_dec(x_24);
return x_101;
}
}
else
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_94, 1);
lean_inc(x_117);
lean_dec(x_94);
x_118 = l_Lean_Meta_Grind_updateLastTag(x_81, x_82, x_83, x_84, x_85, x_86, x_87, x_88, x_117);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_120 = x_118;
} else {
 lean_dec_ref(x_118);
 x_120 = lean_box(0);
}
x_121 = lean_mk_string_unchecked("", 0, 0);
x_122 = l_Lean_stringToMessageData(x_121);
lean_dec(x_121);
lean_inc(x_80);
x_123 = l_Lean_MessageData_ofExpr(x_80);
lean_inc(x_122);
if (lean_is_scalar(x_120)) {
 x_124 = lean_alloc_ctor(7, 2, 0);
} else {
 x_124 = x_120;
 lean_ctor_set_tag(x_124, 7);
}
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_122);
x_126 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_93, x_125, x_85, x_86, x_87, x_88, x_119);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
lean_dec(x_126);
x_50 = x_80;
x_51 = x_81;
x_52 = x_82;
x_53 = x_83;
x_54 = x_84;
x_55 = x_85;
x_56 = x_86;
x_57 = x_87;
x_58 = x_88;
x_59 = x_127;
goto block_79;
}
else
{
lean_dec(x_93);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_25);
lean_dec(x_24);
return x_118;
}
}
}
}
}
else
{
uint8_t x_146; 
lean_dec(x_45);
lean_free_object(x_41);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_146 = !lean_is_exclusive(x_46);
if (x_146 == 0)
{
return x_46;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_46, 0);
x_148 = lean_ctor_get(x_46, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_46);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_150 = lean_ctor_get(x_41, 0);
x_151 = lean_ctor_get(x_41, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_41);
x_152 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_152);
x_153 = l_Lean_Meta_Grind_Goal_getRoot(x_150, x_152, x_8, x_9, x_151);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_218; uint8_t x_219; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_156 = x_153;
} else {
 lean_dec_ref(x_153);
 x_156 = lean_box(0);
}
x_218 = lean_ctor_get(x_24, 0);
lean_inc(x_218);
x_219 = l_Lean_Expr_isAppOf(x_154, x_218);
lean_dec(x_218);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; 
lean_dec(x_156);
lean_dec(x_154);
lean_dec(x_152);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_220 = lean_box(0);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_155);
return x_221;
}
else
{
size_t x_222; size_t x_223; uint8_t x_224; 
x_222 = lean_ptr_addr(x_152);
lean_dec(x_152);
x_223 = lean_ptr_addr(x_154);
x_224 = lean_usize_dec_eq(x_222, x_223);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_225 = l_Lean_Expr_appFn_x21(x_1);
lean_inc(x_154);
x_226 = l_Lean_Expr_app___override(x_225, x_154);
x_227 = l_Lean_Meta_Grind_shareCommon___redArg(x_226, x_5, x_155);
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
x_230 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2, x_229);
lean_dec(x_1);
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
x_233 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_228);
x_234 = lean_grind_internalize(x_228, x_231, x_233, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_232);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; 
x_235 = lean_ctor_get(x_234, 1);
lean_inc(x_235);
lean_dec(x_234);
x_187 = x_228;
x_188 = x_2;
x_189 = x_3;
x_190 = x_4;
x_191 = x_5;
x_192 = x_6;
x_193 = x_7;
x_194 = x_8;
x_195 = x_9;
x_196 = x_235;
goto block_217;
}
else
{
lean_dec(x_228);
lean_dec(x_156);
lean_dec(x_154);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_234;
}
}
else
{
x_187 = x_1;
x_188 = x_2;
x_189 = x_3;
x_190 = x_4;
x_191 = x_5;
x_192 = x_6;
x_193 = x_7;
x_194 = x_8;
x_195 = x_9;
x_196 = x_155;
goto block_217;
}
}
block_186:
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_167 = lean_ctor_get(x_24, 2);
lean_inc(x_167);
lean_dec(x_24);
x_168 = lean_nat_add(x_25, x_167);
lean_dec(x_167);
lean_dec(x_25);
x_169 = l_Lean_Expr_getAppNumArgs(x_154);
x_170 = lean_nat_dec_lt(x_168, x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; 
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_154);
x_171 = lean_box(0);
if (lean_is_scalar(x_156)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_156;
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_166);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_156);
x_173 = lean_nat_sub(x_169, x_168);
lean_dec(x_168);
lean_dec(x_169);
x_174 = lean_nat_sub(x_173, x_26);
lean_dec(x_173);
x_175 = l_Lean_Expr_getRevArg_x21(x_154, x_174);
lean_dec(x_154);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_175);
x_176 = l_Lean_Meta_mkEqRefl(x_175, x_162, x_163, x_164, x_165, x_166);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; lean_object* x_181; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
x_179 = lean_box(0);
x_180 = lean_unbox(x_179);
x_181 = l_Lean_Meta_Grind_pushEqCore(x_157, x_175, x_177, x_180, x_158, x_159, x_160, x_161, x_162, x_163, x_164, x_165, x_178);
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_158);
return x_181;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_175);
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
x_182 = lean_ctor_get(x_176, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_176, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_184 = x_176;
} else {
 lean_dec_ref(x_176);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
}
block_217:
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; 
x_197 = lean_mk_string_unchecked("grind", 5, 5);
x_198 = lean_mk_string_unchecked("debug", 5, 5);
x_199 = lean_mk_string_unchecked("proj", 4, 4);
x_200 = l_Lean_Name_mkStr3(x_197, x_198, x_199);
lean_inc(x_200);
x_201 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_200, x_194, x_196);
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_unbox(x_202);
lean_dec(x_202);
if (x_203 == 0)
{
lean_object* x_204; 
lean_dec(x_200);
x_204 = lean_ctor_get(x_201, 1);
lean_inc(x_204);
lean_dec(x_201);
x_157 = x_187;
x_158 = x_188;
x_159 = x_189;
x_160 = x_190;
x_161 = x_191;
x_162 = x_192;
x_163 = x_193;
x_164 = x_194;
x_165 = x_195;
x_166 = x_204;
goto block_186;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_201, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_206 = x_201;
} else {
 lean_dec_ref(x_201);
 x_206 = lean_box(0);
}
x_207 = l_Lean_Meta_Grind_updateLastTag(x_188, x_189, x_190, x_191, x_192, x_193, x_194, x_195, x_205);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_208 = lean_ctor_get(x_207, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_209 = x_207;
} else {
 lean_dec_ref(x_207);
 x_209 = lean_box(0);
}
x_210 = lean_mk_string_unchecked("", 0, 0);
x_211 = l_Lean_stringToMessageData(x_210);
lean_dec(x_210);
lean_inc(x_187);
x_212 = l_Lean_MessageData_ofExpr(x_187);
lean_inc(x_211);
if (lean_is_scalar(x_209)) {
 x_213 = lean_alloc_ctor(7, 2, 0);
} else {
 x_213 = x_209;
 lean_ctor_set_tag(x_213, 7);
}
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
if (lean_is_scalar(x_206)) {
 x_214 = lean_alloc_ctor(7, 2, 0);
} else {
 x_214 = x_206;
 lean_ctor_set_tag(x_214, 7);
}
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_211);
x_215 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_200, x_214, x_192, x_193, x_194, x_195, x_208);
x_216 = lean_ctor_get(x_215, 1);
lean_inc(x_216);
lean_dec(x_215);
x_157 = x_187;
x_158 = x_188;
x_159 = x_189;
x_160 = x_190;
x_161 = x_191;
x_162 = x_192;
x_163 = x_193;
x_164 = x_194;
x_165 = x_195;
x_166 = x_216;
goto block_186;
}
else
{
lean_dec(x_206);
lean_dec(x_200);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_189);
lean_dec(x_188);
lean_dec(x_187);
lean_dec(x_156);
lean_dec(x_154);
lean_dec(x_25);
lean_dec(x_24);
return x_207;
}
}
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_152);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_236 = lean_ctor_get(x_153, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_153, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_238 = x_153;
} else {
 lean_dec_ref(x_153);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(1, 2, 0);
} else {
 x_239 = x_238;
}
lean_ctor_set(x_239, 0, x_236);
lean_ctor_set(x_239, 1, x_237);
return x_239;
}
}
}
}
else
{
uint8_t x_240; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_240 = !lean_is_exclusive(x_31);
if (x_240 == 0)
{
return x_31;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_241 = lean_ctor_get(x_31, 0);
x_242 = lean_ctor_get(x_31, 1);
lean_inc(x_242);
lean_inc(x_241);
lean_dec(x_31);
x_243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_243, 0, x_241);
lean_ctor_set(x_243, 1, x_242);
return x_243;
}
}
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; 
x_244 = lean_ctor_get(x_13, 1);
lean_inc(x_244);
lean_dec(x_13);
x_245 = lean_ctor_get(x_14, 0);
lean_inc(x_245);
lean_dec(x_14);
x_246 = lean_ctor_get(x_245, 1);
lean_inc(x_246);
x_247 = lean_unsigned_to_nat(1u);
x_248 = lean_nat_add(x_246, x_247);
x_249 = l_Lean_Expr_getAppNumArgs(x_1);
x_250 = lean_nat_dec_eq(x_248, x_249);
lean_dec(x_249);
lean_dec(x_248);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; 
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_251 = lean_box(0);
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_244);
return x_252;
}
else
{
lean_object* x_253; 
lean_inc(x_1);
x_253 = l_Lean_Meta_Grind_isCongrRoot___redArg(x_1, x_2, x_8, x_9, x_244);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; uint8_t x_255; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_unbox(x_254);
lean_dec(x_254);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_256 = lean_ctor_get(x_253, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_257 = x_253;
} else {
 lean_dec_ref(x_253);
 x_257 = lean_box(0);
}
x_258 = lean_box(0);
if (lean_is_scalar(x_257)) {
 x_259 = lean_alloc_ctor(0, 2, 0);
} else {
 x_259 = x_257;
}
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_256);
return x_259;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_260 = lean_ctor_get(x_253, 1);
lean_inc(x_260);
lean_dec(x_253);
x_261 = lean_st_ref_get(x_2, x_260);
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_264 = x_261;
} else {
 lean_dec_ref(x_261);
 x_264 = lean_box(0);
}
x_265 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_265);
x_266 = l_Lean_Meta_Grind_Goal_getRoot(x_262, x_265, x_8, x_9, x_263);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_331; uint8_t x_332; 
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_269 = x_266;
} else {
 lean_dec_ref(x_266);
 x_269 = lean_box(0);
}
x_331 = lean_ctor_get(x_245, 0);
lean_inc(x_331);
x_332 = l_Lean_Expr_isAppOf(x_267, x_331);
lean_dec(x_331);
if (x_332 == 0)
{
lean_object* x_333; lean_object* x_334; 
lean_dec(x_269);
lean_dec(x_267);
lean_dec(x_265);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_333 = lean_box(0);
if (lean_is_scalar(x_264)) {
 x_334 = lean_alloc_ctor(0, 2, 0);
} else {
 x_334 = x_264;
}
lean_ctor_set(x_334, 0, x_333);
lean_ctor_set(x_334, 1, x_268);
return x_334;
}
else
{
size_t x_335; size_t x_336; uint8_t x_337; 
lean_dec(x_264);
x_335 = lean_ptr_addr(x_265);
lean_dec(x_265);
x_336 = lean_ptr_addr(x_267);
x_337 = lean_usize_dec_eq(x_335, x_336);
if (x_337 == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_338 = l_Lean_Expr_appFn_x21(x_1);
lean_inc(x_267);
x_339 = l_Lean_Expr_app___override(x_338, x_267);
x_340 = l_Lean_Meta_Grind_shareCommon___redArg(x_339, x_5, x_268);
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_340, 1);
lean_inc(x_342);
lean_dec(x_340);
x_343 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2, x_342);
lean_dec(x_1);
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_343, 1);
lean_inc(x_345);
lean_dec(x_343);
x_346 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_341);
x_347 = lean_grind_internalize(x_341, x_344, x_346, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_345);
if (lean_obj_tag(x_347) == 0)
{
lean_object* x_348; 
x_348 = lean_ctor_get(x_347, 1);
lean_inc(x_348);
lean_dec(x_347);
x_300 = x_341;
x_301 = x_2;
x_302 = x_3;
x_303 = x_4;
x_304 = x_5;
x_305 = x_6;
x_306 = x_7;
x_307 = x_8;
x_308 = x_9;
x_309 = x_348;
goto block_330;
}
else
{
lean_dec(x_341);
lean_dec(x_269);
lean_dec(x_267);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_347;
}
}
else
{
x_300 = x_1;
x_301 = x_2;
x_302 = x_3;
x_303 = x_4;
x_304 = x_5;
x_305 = x_6;
x_306 = x_7;
x_307 = x_8;
x_308 = x_9;
x_309 = x_268;
goto block_330;
}
}
block_299:
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; 
x_280 = lean_ctor_get(x_245, 2);
lean_inc(x_280);
lean_dec(x_245);
x_281 = lean_nat_add(x_246, x_280);
lean_dec(x_280);
lean_dec(x_246);
x_282 = l_Lean_Expr_getAppNumArgs(x_267);
x_283 = lean_nat_dec_lt(x_281, x_282);
if (x_283 == 0)
{
lean_object* x_284; lean_object* x_285; 
lean_dec(x_282);
lean_dec(x_281);
lean_dec(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec(x_272);
lean_dec(x_271);
lean_dec(x_270);
lean_dec(x_267);
x_284 = lean_box(0);
if (lean_is_scalar(x_269)) {
 x_285 = lean_alloc_ctor(0, 2, 0);
} else {
 x_285 = x_269;
}
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_279);
return x_285;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_dec(x_269);
x_286 = lean_nat_sub(x_282, x_281);
lean_dec(x_281);
lean_dec(x_282);
x_287 = lean_nat_sub(x_286, x_247);
lean_dec(x_286);
x_288 = l_Lean_Expr_getRevArg_x21(x_267, x_287);
lean_dec(x_267);
lean_inc(x_278);
lean_inc(x_277);
lean_inc(x_276);
lean_inc(x_275);
lean_inc(x_288);
x_289 = l_Lean_Meta_mkEqRefl(x_288, x_275, x_276, x_277, x_278, x_279);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; lean_object* x_294; 
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_289, 1);
lean_inc(x_291);
lean_dec(x_289);
x_292 = lean_box(0);
x_293 = lean_unbox(x_292);
x_294 = l_Lean_Meta_Grind_pushEqCore(x_270, x_288, x_290, x_293, x_271, x_272, x_273, x_274, x_275, x_276, x_277, x_278, x_291);
lean_dec(x_274);
lean_dec(x_273);
lean_dec(x_272);
lean_dec(x_271);
return x_294;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
lean_dec(x_288);
lean_dec(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec(x_272);
lean_dec(x_271);
lean_dec(x_270);
x_295 = lean_ctor_get(x_289, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_289, 1);
lean_inc(x_296);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 x_297 = x_289;
} else {
 lean_dec_ref(x_289);
 x_297 = lean_box(0);
}
if (lean_is_scalar(x_297)) {
 x_298 = lean_alloc_ctor(1, 2, 0);
} else {
 x_298 = x_297;
}
lean_ctor_set(x_298, 0, x_295);
lean_ctor_set(x_298, 1, x_296);
return x_298;
}
}
}
block_330:
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; uint8_t x_316; 
x_310 = lean_mk_string_unchecked("grind", 5, 5);
x_311 = lean_mk_string_unchecked("debug", 5, 5);
x_312 = lean_mk_string_unchecked("proj", 4, 4);
x_313 = l_Lean_Name_mkStr3(x_310, x_311, x_312);
lean_inc(x_313);
x_314 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_313, x_307, x_309);
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_unbox(x_315);
lean_dec(x_315);
if (x_316 == 0)
{
lean_object* x_317; 
lean_dec(x_313);
x_317 = lean_ctor_get(x_314, 1);
lean_inc(x_317);
lean_dec(x_314);
x_270 = x_300;
x_271 = x_301;
x_272 = x_302;
x_273 = x_303;
x_274 = x_304;
x_275 = x_305;
x_276 = x_306;
x_277 = x_307;
x_278 = x_308;
x_279 = x_317;
goto block_299;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_318 = lean_ctor_get(x_314, 1);
lean_inc(x_318);
if (lean_is_exclusive(x_314)) {
 lean_ctor_release(x_314, 0);
 lean_ctor_release(x_314, 1);
 x_319 = x_314;
} else {
 lean_dec_ref(x_314);
 x_319 = lean_box(0);
}
x_320 = l_Lean_Meta_Grind_updateLastTag(x_301, x_302, x_303, x_304, x_305, x_306, x_307, x_308, x_318);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_321 = lean_ctor_get(x_320, 1);
lean_inc(x_321);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 lean_ctor_release(x_320, 1);
 x_322 = x_320;
} else {
 lean_dec_ref(x_320);
 x_322 = lean_box(0);
}
x_323 = lean_mk_string_unchecked("", 0, 0);
x_324 = l_Lean_stringToMessageData(x_323);
lean_dec(x_323);
lean_inc(x_300);
x_325 = l_Lean_MessageData_ofExpr(x_300);
lean_inc(x_324);
if (lean_is_scalar(x_322)) {
 x_326 = lean_alloc_ctor(7, 2, 0);
} else {
 x_326 = x_322;
 lean_ctor_set_tag(x_326, 7);
}
lean_ctor_set(x_326, 0, x_324);
lean_ctor_set(x_326, 1, x_325);
if (lean_is_scalar(x_319)) {
 x_327 = lean_alloc_ctor(7, 2, 0);
} else {
 x_327 = x_319;
 lean_ctor_set_tag(x_327, 7);
}
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_324);
x_328 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_313, x_327, x_305, x_306, x_307, x_308, x_321);
x_329 = lean_ctor_get(x_328, 1);
lean_inc(x_329);
lean_dec(x_328);
x_270 = x_300;
x_271 = x_301;
x_272 = x_302;
x_273 = x_303;
x_274 = x_304;
x_275 = x_305;
x_276 = x_306;
x_277 = x_307;
x_278 = x_308;
x_279 = x_329;
goto block_299;
}
else
{
lean_dec(x_319);
lean_dec(x_313);
lean_dec(x_308);
lean_dec(x_307);
lean_dec(x_306);
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_302);
lean_dec(x_301);
lean_dec(x_300);
lean_dec(x_269);
lean_dec(x_267);
lean_dec(x_246);
lean_dec(x_245);
return x_320;
}
}
}
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
lean_dec(x_265);
lean_dec(x_264);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_349 = lean_ctor_get(x_266, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_266, 1);
lean_inc(x_350);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_351 = x_266;
} else {
 lean_dec_ref(x_266);
 x_351 = lean_box(0);
}
if (lean_is_scalar(x_351)) {
 x_352 = lean_alloc_ctor(1, 2, 0);
} else {
 x_352 = x_351;
}
lean_ctor_set(x_352, 0, x_349);
lean_ctor_set(x_352, 1, x_350);
return x_352;
}
}
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_353 = lean_ctor_get(x_253, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_253, 1);
lean_inc(x_354);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_355 = x_253;
} else {
 lean_dec_ref(x_253);
 x_355 = lean_box(0);
}
if (lean_is_scalar(x_355)) {
 x_356 = lean_alloc_ctor(1, 2, 0);
} else {
 x_356 = x_355;
}
lean_ctor_set(x_356, 0, x_353);
lean_ctor_set(x_356, 1, x_354);
return x_356;
}
}
}
}
}
else
{
lean_object* x_357; lean_object* x_358; 
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
x_357 = lean_box(0);
x_358 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_358, 0, x_357);
lean_ctor_set(x_358, 1, x_10);
return x_358;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Meta_Grind_propagateProjEq_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getProjectionFnInfo_x3f___at___Lean_Meta_Grind_propagateProjEq_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Meta_Grind_propagateProjEq_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_getProjectionFnInfo_x3f___at___Lean_Meta_Grind_propagateProjEq_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* initialize_Lean_ProjFns(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Internalize(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Proj(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_ProjFns(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Internalize(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
