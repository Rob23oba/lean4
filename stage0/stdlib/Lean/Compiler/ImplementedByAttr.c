// Lean compiler output
// Module: Lean.Compiler.ImplementedByAttr
// Imports: Lean.Attributes Lean.Declaration Lean.MonadEnv Lean.Elab.InfoTree
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
lean_object* l_Lean_Core_instantiateTypeLevelParams___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_Lean_setEnv___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn___lam__2____x40_Lean_Compiler_ImplementedByAttr___hyg_3_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* lean_get_implemented_by(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_ImplementedByAttr___hyg_3_(lean_object*);
lean_object* l_Lean_Attribute_Builtin_getIdent(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setImplementedBy(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Elab_addConstInfo___at___Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn___lam__0____x40_Lean_Compiler_ImplementedByAttr___hyg_3_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_setImplementedBy(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_getConstVal___at___Lean_mkConstWithLevelParams___at___Lean_Elab_addConstInfo___at___Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn___lam__1____x40_Lean_Compiler_ImplementedByAttr___hyg_3_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn___lam__0____x40_Lean_Compiler_ImplementedByAttr___hyg_3____boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_implementedByAttr;
lean_object* l_List_lengthTR(lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_____private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
lean_object* l_Lean_registerParametricAttribute(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn___lam__1____x40_Lean_Compiler_ImplementedByAttr___hyg_3____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn___lam__0____x40_Lean_Compiler_ImplementedByAttr___hyg_3_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn___lam__1____x40_Lean_Compiler_ImplementedByAttr___hyg_3_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn___lam__2____x40_Lean_Compiler_ImplementedByAttr___hyg_3_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_1);
x_6 = l_Lean_getConstInfo___at_____private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Attribute_Builtin_getIdent(x_2, x_3, x_4, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
lean_inc(x_4);
lean_inc(x_3);
x_13 = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(x_10, x_12, x_3, x_4, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
x_17 = l_Lean_getConstVal___at___Lean_mkConstWithLevelParams___at___Lean_Elab_addConstInfo___at___Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__0(x_15, x_3, x_4, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_ConstantInfo_levelParams(x_7);
x_21 = l_List_lengthTR(lean_box(0), x_20);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
x_23 = l_List_lengthTR(lean_box(0), x_22);
lean_dec(x_22);
x_24 = lean_nat_dec_eq(x_21, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_7);
x_25 = lean_mk_string_unchecked("invalid 'implemented_by' argument '", 35, 35);
x_26 = l_Lean_stringToMessageData(x_25);
lean_dec(x_25);
x_27 = l_Lean_MessageData_ofName(x_15);
lean_inc(x_27);
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_27);
lean_ctor_set(x_13, 0, x_26);
x_28 = lean_mk_string_unchecked("', '", 4, 4);
x_29 = l_Lean_stringToMessageData(x_28);
lean_dec(x_28);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_13);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
x_32 = lean_mk_string_unchecked("' has ", 6, 6);
x_33 = l_Lean_stringToMessageData(x_32);
lean_dec(x_32);
lean_inc(x_33);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_35 = l___private_Init_Data_Repr_0__Nat_reprFast(x_23);
x_36 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = l_Lean_MessageData_ofFormat(x_36);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_mk_string_unchecked(" universe level parameter(s), but '", 35, 35);
x_40 = l_Lean_stringToMessageData(x_39);
lean_dec(x_39);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_MessageData_ofName(x_1);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_33);
x_45 = l___private_Init_Data_Repr_0__Nat_reprFast(x_21);
x_46 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = l_Lean_MessageData_ofFormat(x_46);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_mk_string_unchecked("", 0, 0);
x_50 = l_Lean_stringToMessageData(x_49);
lean_dec(x_49);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_51, x_3, x_4, x_19);
lean_dec(x_4);
lean_dec(x_3);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
return x_52;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_52);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_dec(x_23);
lean_dec(x_21);
x_57 = lean_box(0);
x_58 = l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Elab_addConstInfo___at___Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(x_20, x_57);
lean_inc(x_18);
x_59 = l_Lean_Core_instantiateTypeLevelParams___redArg(x_18, x_58, x_4, x_19);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_ctor_get(x_59, 1);
x_63 = l_Lean_ConstantInfo_type(x_7);
x_64 = lean_expr_eqv(x_63, x_61);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
lean_free_object(x_59);
lean_dec(x_18);
lean_dec(x_7);
x_65 = lean_mk_string_unchecked("invalid 'implemented_by' argument '", 35, 35);
x_66 = l_Lean_stringToMessageData(x_65);
lean_dec(x_65);
x_67 = l_Lean_MessageData_ofName(x_15);
lean_inc(x_67);
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_67);
lean_ctor_set(x_13, 0, x_66);
x_68 = lean_mk_string_unchecked("', '", 4, 4);
x_69 = l_Lean_stringToMessageData(x_68);
lean_dec(x_68);
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_13);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_67);
x_72 = lean_mk_string_unchecked("' has type", 10, 10);
x_73 = l_Lean_stringToMessageData(x_72);
lean_dec(x_72);
lean_inc(x_73);
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_indentExpr(x_61);
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_mk_string_unchecked("\nbut '", 6, 6);
x_78 = l_Lean_stringToMessageData(x_77);
lean_dec(x_77);
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_MessageData_ofName(x_1);
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_73);
x_83 = l_Lean_indentExpr(x_63);
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_mk_string_unchecked("", 0, 0);
x_86 = l_Lean_stringToMessageData(x_85);
lean_dec(x_85);
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_87, x_3, x_4, x_62);
lean_dec(x_4);
lean_dec(x_3);
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
return x_88;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_88, 0);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_88);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
lean_dec(x_63);
lean_dec(x_61);
lean_dec(x_1);
x_93 = l_Lean_ConstantInfo_name(x_7);
lean_dec(x_7);
x_94 = lean_ctor_get(x_18, 0);
lean_inc(x_94);
lean_dec(x_18);
x_95 = lean_name_eq(x_93, x_94);
lean_dec(x_94);
lean_dec(x_93);
if (x_95 == 0)
{
lean_free_object(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_59, 0, x_15);
return x_59;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
lean_free_object(x_59);
x_96 = lean_mk_string_unchecked("invalid 'implemented_by' argument '", 35, 35);
x_97 = l_Lean_stringToMessageData(x_96);
lean_dec(x_96);
x_98 = l_Lean_MessageData_ofName(x_15);
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_98);
lean_ctor_set(x_13, 0, x_97);
x_99 = lean_mk_string_unchecked("', function cannot be implemented by itself", 43, 43);
x_100 = l_Lean_stringToMessageData(x_99);
lean_dec(x_99);
x_101 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_101, 0, x_13);
lean_ctor_set(x_101, 1, x_100);
x_102 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_101, x_3, x_4, x_62);
lean_dec(x_4);
lean_dec(x_3);
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
return x_102;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_102, 0);
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_102);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_107 = lean_ctor_get(x_59, 0);
x_108 = lean_ctor_get(x_59, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_59);
x_109 = l_Lean_ConstantInfo_type(x_7);
x_110 = lean_expr_eqv(x_109, x_107);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_18);
lean_dec(x_7);
x_111 = lean_mk_string_unchecked("invalid 'implemented_by' argument '", 35, 35);
x_112 = l_Lean_stringToMessageData(x_111);
lean_dec(x_111);
x_113 = l_Lean_MessageData_ofName(x_15);
lean_inc(x_113);
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_113);
lean_ctor_set(x_13, 0, x_112);
x_114 = lean_mk_string_unchecked("', '", 4, 4);
x_115 = l_Lean_stringToMessageData(x_114);
lean_dec(x_114);
x_116 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_116, 0, x_13);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_113);
x_118 = lean_mk_string_unchecked("' has type", 10, 10);
x_119 = l_Lean_stringToMessageData(x_118);
lean_dec(x_118);
lean_inc(x_119);
x_120 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_119);
x_121 = l_Lean_indentExpr(x_107);
x_122 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_mk_string_unchecked("\nbut '", 6, 6);
x_124 = l_Lean_stringToMessageData(x_123);
lean_dec(x_123);
x_125 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_124);
x_126 = l_Lean_MessageData_ofName(x_1);
x_127 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_119);
x_129 = l_Lean_indentExpr(x_109);
x_130 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_mk_string_unchecked("", 0, 0);
x_132 = l_Lean_stringToMessageData(x_131);
lean_dec(x_131);
x_133 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_132);
x_134 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_133, x_3, x_4, x_108);
lean_dec(x_4);
lean_dec(x_3);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_137 = x_134;
} else {
 lean_dec_ref(x_134);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_136);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; 
lean_dec(x_109);
lean_dec(x_107);
lean_dec(x_1);
x_139 = l_Lean_ConstantInfo_name(x_7);
lean_dec(x_7);
x_140 = lean_ctor_get(x_18, 0);
lean_inc(x_140);
lean_dec(x_18);
x_141 = lean_name_eq(x_139, x_140);
lean_dec(x_140);
lean_dec(x_139);
if (x_141 == 0)
{
lean_object* x_142; 
lean_free_object(x_13);
lean_dec(x_4);
lean_dec(x_3);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_15);
lean_ctor_set(x_142, 1, x_108);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_143 = lean_mk_string_unchecked("invalid 'implemented_by' argument '", 35, 35);
x_144 = l_Lean_stringToMessageData(x_143);
lean_dec(x_143);
x_145 = l_Lean_MessageData_ofName(x_15);
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_145);
lean_ctor_set(x_13, 0, x_144);
x_146 = lean_mk_string_unchecked("', function cannot be implemented by itself", 43, 43);
x_147 = l_Lean_stringToMessageData(x_146);
lean_dec(x_146);
x_148 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_148, 0, x_13);
lean_ctor_set(x_148, 1, x_147);
x_149 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_148, x_3, x_4, x_108);
lean_dec(x_4);
lean_dec(x_3);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_152 = x_149;
} else {
 lean_dec_ref(x_149);
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
}
}
else
{
uint8_t x_154; 
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_154 = !lean_is_exclusive(x_17);
if (x_154 == 0)
{
return x_17;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_17, 0);
x_156 = lean_ctor_get(x_17, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_17);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_13, 0);
x_159 = lean_ctor_get(x_13, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_13);
lean_inc(x_158);
x_160 = l_Lean_getConstVal___at___Lean_mkConstWithLevelParams___at___Lean_Elab_addConstInfo___at___Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__0(x_158, x_3, x_4, x_159);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_163 = l_Lean_ConstantInfo_levelParams(x_7);
x_164 = l_List_lengthTR(lean_box(0), x_163);
x_165 = lean_ctor_get(x_161, 1);
lean_inc(x_165);
x_166 = l_List_lengthTR(lean_box(0), x_165);
lean_dec(x_165);
x_167 = lean_nat_dec_eq(x_164, x_166);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_163);
lean_dec(x_161);
lean_dec(x_7);
x_168 = lean_mk_string_unchecked("invalid 'implemented_by' argument '", 35, 35);
x_169 = l_Lean_stringToMessageData(x_168);
lean_dec(x_168);
x_170 = l_Lean_MessageData_ofName(x_158);
lean_inc(x_170);
x_171 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
x_172 = lean_mk_string_unchecked("', '", 4, 4);
x_173 = l_Lean_stringToMessageData(x_172);
lean_dec(x_172);
x_174 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_173);
x_175 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_170);
x_176 = lean_mk_string_unchecked("' has ", 6, 6);
x_177 = l_Lean_stringToMessageData(x_176);
lean_dec(x_176);
lean_inc(x_177);
x_178 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_177);
x_179 = l___private_Init_Data_Repr_0__Nat_reprFast(x_166);
x_180 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_180, 0, x_179);
x_181 = l_Lean_MessageData_ofFormat(x_180);
x_182 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_182, 0, x_178);
lean_ctor_set(x_182, 1, x_181);
x_183 = lean_mk_string_unchecked(" universe level parameter(s), but '", 35, 35);
x_184 = l_Lean_stringToMessageData(x_183);
lean_dec(x_183);
x_185 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_184);
x_186 = l_Lean_MessageData_ofName(x_1);
x_187 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
x_188 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_177);
x_189 = l___private_Init_Data_Repr_0__Nat_reprFast(x_164);
x_190 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_190, 0, x_189);
x_191 = l_Lean_MessageData_ofFormat(x_190);
x_192 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_192, 0, x_188);
lean_ctor_set(x_192, 1, x_191);
x_193 = lean_mk_string_unchecked("", 0, 0);
x_194 = l_Lean_stringToMessageData(x_193);
lean_dec(x_193);
x_195 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_194);
x_196 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_195, x_3, x_4, x_162);
lean_dec(x_4);
lean_dec(x_3);
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_199 = x_196;
} else {
 lean_dec_ref(x_196);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(1, 2, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_197);
lean_ctor_set(x_200, 1, x_198);
return x_200;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; 
lean_dec(x_166);
lean_dec(x_164);
x_201 = lean_box(0);
x_202 = l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Elab_addConstInfo___at___Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(x_163, x_201);
lean_inc(x_161);
x_203 = l_Lean_Core_instantiateTypeLevelParams___redArg(x_161, x_202, x_4, x_162);
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_206 = x_203;
} else {
 lean_dec_ref(x_203);
 x_206 = lean_box(0);
}
x_207 = l_Lean_ConstantInfo_type(x_7);
x_208 = lean_expr_eqv(x_207, x_204);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_206);
lean_dec(x_161);
lean_dec(x_7);
x_209 = lean_mk_string_unchecked("invalid 'implemented_by' argument '", 35, 35);
x_210 = l_Lean_stringToMessageData(x_209);
lean_dec(x_209);
x_211 = l_Lean_MessageData_ofName(x_158);
lean_inc(x_211);
x_212 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
x_213 = lean_mk_string_unchecked("', '", 4, 4);
x_214 = l_Lean_stringToMessageData(x_213);
lean_dec(x_213);
x_215 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_215, 0, x_212);
lean_ctor_set(x_215, 1, x_214);
x_216 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_211);
x_217 = lean_mk_string_unchecked("' has type", 10, 10);
x_218 = l_Lean_stringToMessageData(x_217);
lean_dec(x_217);
lean_inc(x_218);
x_219 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_219, 0, x_216);
lean_ctor_set(x_219, 1, x_218);
x_220 = l_Lean_indentExpr(x_204);
x_221 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
x_222 = lean_mk_string_unchecked("\nbut '", 6, 6);
x_223 = l_Lean_stringToMessageData(x_222);
lean_dec(x_222);
x_224 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_224, 0, x_221);
lean_ctor_set(x_224, 1, x_223);
x_225 = l_Lean_MessageData_ofName(x_1);
x_226 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_225);
x_227 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_218);
x_228 = l_Lean_indentExpr(x_207);
x_229 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
x_230 = lean_mk_string_unchecked("", 0, 0);
x_231 = l_Lean_stringToMessageData(x_230);
lean_dec(x_230);
x_232 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_232, 0, x_229);
lean_ctor_set(x_232, 1, x_231);
x_233 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_232, x_3, x_4, x_205);
lean_dec(x_4);
lean_dec(x_3);
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_236 = x_233;
} else {
 lean_dec_ref(x_233);
 x_236 = lean_box(0);
}
if (lean_is_scalar(x_236)) {
 x_237 = lean_alloc_ctor(1, 2, 0);
} else {
 x_237 = x_236;
}
lean_ctor_set(x_237, 0, x_234);
lean_ctor_set(x_237, 1, x_235);
return x_237;
}
else
{
lean_object* x_238; lean_object* x_239; uint8_t x_240; 
lean_dec(x_207);
lean_dec(x_204);
lean_dec(x_1);
x_238 = l_Lean_ConstantInfo_name(x_7);
lean_dec(x_7);
x_239 = lean_ctor_get(x_161, 0);
lean_inc(x_239);
lean_dec(x_161);
x_240 = lean_name_eq(x_238, x_239);
lean_dec(x_239);
lean_dec(x_238);
if (x_240 == 0)
{
lean_object* x_241; 
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_206)) {
 x_241 = lean_alloc_ctor(0, 2, 0);
} else {
 x_241 = x_206;
}
lean_ctor_set(x_241, 0, x_158);
lean_ctor_set(x_241, 1, x_205);
return x_241;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_206);
x_242 = lean_mk_string_unchecked("invalid 'implemented_by' argument '", 35, 35);
x_243 = l_Lean_stringToMessageData(x_242);
lean_dec(x_242);
x_244 = l_Lean_MessageData_ofName(x_158);
x_245 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
x_246 = lean_mk_string_unchecked("', function cannot be implemented by itself", 43, 43);
x_247 = l_Lean_stringToMessageData(x_246);
lean_dec(x_246);
x_248 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_248, 0, x_245);
lean_ctor_set(x_248, 1, x_247);
x_249 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_248, x_3, x_4, x_205);
lean_dec(x_4);
lean_dec(x_3);
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 x_252 = x_249;
} else {
 lean_dec_ref(x_249);
 x_252 = lean_box(0);
}
if (lean_is_scalar(x_252)) {
 x_253 = lean_alloc_ctor(1, 2, 0);
} else {
 x_253 = x_252;
}
lean_ctor_set(x_253, 0, x_250);
lean_ctor_set(x_253, 1, x_251);
return x_253;
}
}
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_158);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_254 = lean_ctor_get(x_160, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_160, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_256 = x_160;
} else {
 lean_dec_ref(x_160);
 x_256 = lean_box(0);
}
if (lean_is_scalar(x_256)) {
 x_257 = lean_alloc_ctor(1, 2, 0);
} else {
 x_257 = x_256;
}
lean_ctor_set(x_257, 0, x_254);
lean_ctor_set(x_257, 1, x_255);
return x_257;
}
}
}
else
{
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
else
{
uint8_t x_258; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_258 = !lean_is_exclusive(x_9);
if (x_258 == 0)
{
return x_9;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_9, 0);
x_260 = lean_ctor_get(x_9, 1);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_9);
x_261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_261, 0, x_259);
lean_ctor_set(x_261, 1, x_260);
return x_261;
}
}
}
else
{
uint8_t x_262; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_262 = !lean_is_exclusive(x_6);
if (x_262 == 0)
{
return x_6;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_6, 0);
x_264 = lean_ctor_get(x_6, 1);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_6);
x_265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
return x_265;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_ImplementedByAttr___hyg_3_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_initFn___lam__0____x40_Lean_Compiler_ImplementedByAttr___hyg_3____boxed), 3, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_initFn___lam__1____x40_Lean_Compiler_ImplementedByAttr___hyg_3____boxed), 5, 0);
x_4 = lean_alloc_closure((void*)(l_Lean_Compiler_initFn___lam__2____x40_Lean_Compiler_ImplementedByAttr___hyg_3_), 5, 0);
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("Compiler", 8, 8);
x_7 = lean_mk_string_unchecked("implementedByAttr", 17, 17);
x_8 = l_Lean_Name_mkStr3(x_5, x_6, x_7);
x_9 = lean_mk_string_unchecked("implemented_by", 14, 14);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_mk_string_unchecked("name of the Lean (probably unsafe) function that implements opaque constant", 75, 75);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
x_14 = lean_unbox(x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*3, x_14);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_4);
lean_ctor_set(x_15, 2, x_3);
lean_ctor_set(x_15, 3, x_2);
x_16 = l_Lean_registerParametricAttribute(lean_box(0), x_15, x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn___lam__0____x40_Lean_Compiler_ImplementedByAttr___hyg_3____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_initFn___lam__0____x40_Lean_Compiler_ImplementedByAttr___hyg_3_(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn___lam__1____x40_Lean_Compiler_ImplementedByAttr___hyg_3____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_initFn___lam__1____x40_Lean_Compiler_ImplementedByAttr___hyg_3_(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* lean_get_implemented_by(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = l_Lean_Compiler_implementedByAttr;
x_5 = l_Lean_ParametricAttribute_getParam_x3f___redArg(x_3, x_4, x_1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_setImplementedBy(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Compiler_implementedByAttr;
x_5 = l_Lean_ParametricAttribute_setParam___redArg(x_4, x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_setImplementedBy(x_6, x_1, x_2);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_ctor_set_tag(x_7, 3);
x_9 = l_Lean_MessageData_ofFormat(x_7);
x_10 = l_Lean_throwError___redArg(x_3, x_4, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Lean_MessageData_ofFormat(x_12);
x_14 = l_Lean_throwError___redArg(x_3, x_4, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
lean_dec(x_3);
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
lean_dec(x_7);
x_16 = l_Lean_setEnv___redArg(x_5, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_2);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_setImplementedBy___redArg___lam__0), 6, 5);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
lean_closure_set(x_6, 2, x_1);
lean_closure_set(x_6, 3, x_3);
lean_closure_set(x_6, 4, x_2);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_setImplementedBy___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* initialize_Lean_Attributes(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Declaration(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_MonadEnv(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_InfoTree(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_ImplementedByAttr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Attributes(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Declaration(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_MonadEnv(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_InfoTree(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_Compiler_initFn____x40_Lean_Compiler_ImplementedByAttr___hyg_3_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_implementedByAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_implementedByAttr);
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
