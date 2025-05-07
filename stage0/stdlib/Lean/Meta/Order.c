// Lean compiler output
// Module: Lean.Meta.Order
// Imports: Lean.Meta.InferType Lean.Meta.PProdN Lean.Meta.AppBuilder Init.Internal.Order.Basic
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
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkInstCompleteLatticePProd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Meta_PProdN_genMk___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_toPartialOrder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Meta_mkPackedPPRodInstance_spec__1(lean_object*, size_t, size_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkPackedPPRodInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_mkPackedPPRodInstance_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Meta_mkPackedPPRodInstance_spec__2(uint8_t, lean_object*, size_t, size_t);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkFixOfMonFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Meta_mkPackedPPRodInstance_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkInstCCPOPProd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkInstPiOfInstForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Meta_mkPackedPPRodInstance_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_mkPackedPPRodInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkInstPiOfInstForall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_8 = lean_infer_type(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_mk_string_unchecked("Lean", 4, 4);
x_13 = lean_mk_string_unchecked("Order", 5, 5);
x_14 = lean_mk_string_unchecked("CCPO", 4, 4);
lean_inc(x_13);
lean_inc(x_12);
x_15 = l_Lean_Name_mkStr3(x_12, x_13, x_14);
x_16 = l_Lean_Expr_isAppOf(x_10, x_15);
lean_dec(x_15);
lean_dec(x_10);
x_17 = lean_box(1);
if (x_16 == 0)
{
lean_object* x_18; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_18 = lean_infer_type(x_2, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_mk_string_unchecked("CompleteLattice", 15, 15);
lean_inc(x_13);
lean_inc(x_12);
x_23 = l_Lean_Name_mkStr3(x_12, x_13, x_22);
x_24 = l_Lean_Expr_isAppOf(x_20, x_23);
lean_dec(x_23);
lean_dec(x_20);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
x_25 = lean_mk_string_unchecked("mkInstPiOfInstForall: unexpected type of ", 41, 41);
x_26 = l_Lean_stringToMessageData(x_25);
lean_dec(x_25);
x_27 = l_Lean_MessageData_ofExpr(x_2);
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_27);
lean_ctor_set(x_18, 0, x_26);
x_28 = lean_mk_string_unchecked("", 0, 0);
x_29 = l_Lean_stringToMessageData(x_28);
lean_dec(x_28);
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_29);
lean_ctor_set(x_8, 0, x_18);
x_30 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_8, x_3, x_4, x_5, x_6, x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_30;
}
else
{
lean_object* x_31; 
lean_free_object(x_18);
lean_free_object(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_31 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_21);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; lean_object* x_40; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_mk_empty_array_with_capacity(x_34);
x_36 = lean_array_push(x_35, x_1);
x_37 = lean_box(1);
x_38 = lean_unbox(x_17);
x_39 = lean_unbox(x_37);
x_40 = l_Lean_Meta_mkLambdaFVars(x_36, x_2, x_16, x_38, x_16, x_39, x_3, x_4, x_5, x_6, x_33);
lean_dec(x_36);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_mk_string_unchecked("instCompleteLatticePi", 21, 21);
x_44 = l_Lean_Name_mkStr3(x_12, x_13, x_43);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_32);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_41);
x_48 = lean_unsigned_to_nat(3u);
x_49 = lean_mk_empty_array_with_capacity(x_48);
x_50 = lean_array_push(x_49, x_45);
x_51 = lean_array_push(x_50, x_46);
x_52 = lean_array_push(x_51, x_47);
x_53 = l_Lean_Meta_mkAppOptM(x_44, x_52, x_3, x_4, x_5, x_6, x_42);
return x_53;
}
else
{
lean_dec(x_32);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_40;
}
}
else
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_31;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_18, 0);
x_55 = lean_ctor_get(x_18, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_18);
x_56 = lean_mk_string_unchecked("CompleteLattice", 15, 15);
lean_inc(x_13);
lean_inc(x_12);
x_57 = l_Lean_Name_mkStr3(x_12, x_13, x_56);
x_58 = l_Lean_Expr_isAppOf(x_54, x_57);
lean_dec(x_57);
lean_dec(x_54);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
x_59 = lean_mk_string_unchecked("mkInstPiOfInstForall: unexpected type of ", 41, 41);
x_60 = l_Lean_stringToMessageData(x_59);
lean_dec(x_59);
x_61 = l_Lean_MessageData_ofExpr(x_2);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_mk_string_unchecked("", 0, 0);
x_64 = l_Lean_stringToMessageData(x_63);
lean_dec(x_63);
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_64);
lean_ctor_set(x_8, 0, x_62);
x_65 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_8, x_3, x_4, x_5, x_6, x_55);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_65;
}
else
{
lean_object* x_66; 
lean_free_object(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_66 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_55);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_74; lean_object* x_75; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_unsigned_to_nat(1u);
x_70 = lean_mk_empty_array_with_capacity(x_69);
x_71 = lean_array_push(x_70, x_1);
x_72 = lean_box(1);
x_73 = lean_unbox(x_17);
x_74 = lean_unbox(x_72);
x_75 = l_Lean_Meta_mkLambdaFVars(x_71, x_2, x_16, x_73, x_16, x_74, x_3, x_4, x_5, x_6, x_68);
lean_dec(x_71);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_mk_string_unchecked("instCompleteLatticePi", 21, 21);
x_79 = l_Lean_Name_mkStr3(x_12, x_13, x_78);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_67);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_76);
x_83 = lean_unsigned_to_nat(3u);
x_84 = lean_mk_empty_array_with_capacity(x_83);
x_85 = lean_array_push(x_84, x_80);
x_86 = lean_array_push(x_85, x_81);
x_87 = lean_array_push(x_86, x_82);
x_88 = l_Lean_Meta_mkAppOptM(x_79, x_87, x_3, x_4, x_5, x_6, x_77);
return x_88;
}
else
{
lean_dec(x_67);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_75;
}
}
else
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_66;
}
}
}
}
else
{
lean_dec(x_13);
lean_dec(x_12);
lean_free_object(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
else
{
lean_object* x_89; 
lean_free_object(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_89 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; uint8_t x_98; uint8_t x_99; uint8_t x_100; lean_object* x_101; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_unsigned_to_nat(1u);
x_93 = lean_mk_empty_array_with_capacity(x_92);
x_94 = lean_array_push(x_93, x_1);
x_95 = lean_box(0);
x_96 = lean_box(1);
x_97 = lean_unbox(x_95);
x_98 = lean_unbox(x_17);
x_99 = lean_unbox(x_95);
x_100 = lean_unbox(x_96);
x_101 = l_Lean_Meta_mkLambdaFVars(x_94, x_2, x_97, x_98, x_99, x_100, x_3, x_4, x_5, x_6, x_91);
lean_dec(x_94);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_mk_string_unchecked("instCCPOPi", 10, 10);
x_105 = l_Lean_Name_mkStr3(x_12, x_13, x_104);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_90);
x_107 = lean_box(0);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_102);
x_109 = lean_unsigned_to_nat(3u);
x_110 = lean_mk_empty_array_with_capacity(x_109);
x_111 = lean_array_push(x_110, x_106);
x_112 = lean_array_push(x_111, x_107);
x_113 = lean_array_push(x_112, x_108);
x_114 = l_Lean_Meta_mkAppOptM(x_105, x_113, x_3, x_4, x_5, x_6, x_103);
return x_114;
}
else
{
lean_dec(x_90);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_101;
}
}
else
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_89;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; 
x_115 = lean_ctor_get(x_8, 0);
x_116 = lean_ctor_get(x_8, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_8);
x_117 = lean_mk_string_unchecked("Lean", 4, 4);
x_118 = lean_mk_string_unchecked("Order", 5, 5);
x_119 = lean_mk_string_unchecked("CCPO", 4, 4);
lean_inc(x_118);
lean_inc(x_117);
x_120 = l_Lean_Name_mkStr3(x_117, x_118, x_119);
x_121 = l_Lean_Expr_isAppOf(x_115, x_120);
lean_dec(x_120);
lean_dec(x_115);
x_122 = lean_box(1);
if (x_121 == 0)
{
lean_object* x_123; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_123 = lean_infer_type(x_2, x_3, x_4, x_5, x_6, x_116);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_126 = x_123;
} else {
 lean_dec_ref(x_123);
 x_126 = lean_box(0);
}
x_127 = lean_mk_string_unchecked("CompleteLattice", 15, 15);
lean_inc(x_118);
lean_inc(x_117);
x_128 = l_Lean_Name_mkStr3(x_117, x_118, x_127);
x_129 = l_Lean_Expr_isAppOf(x_124, x_128);
lean_dec(x_128);
lean_dec(x_124);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_1);
x_130 = lean_mk_string_unchecked("mkInstPiOfInstForall: unexpected type of ", 41, 41);
x_131 = l_Lean_stringToMessageData(x_130);
lean_dec(x_130);
x_132 = l_Lean_MessageData_ofExpr(x_2);
if (lean_is_scalar(x_126)) {
 x_133 = lean_alloc_ctor(7, 2, 0);
} else {
 x_133 = x_126;
 lean_ctor_set_tag(x_133, 7);
}
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_mk_string_unchecked("", 0, 0);
x_135 = l_Lean_stringToMessageData(x_134);
lean_dec(x_134);
x_136 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_135);
x_137 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_136, x_3, x_4, x_5, x_6, x_125);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_137;
}
else
{
lean_object* x_138; 
lean_dec(x_126);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_138 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_125);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; uint8_t x_146; lean_object* x_147; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_141 = lean_unsigned_to_nat(1u);
x_142 = lean_mk_empty_array_with_capacity(x_141);
x_143 = lean_array_push(x_142, x_1);
x_144 = lean_box(1);
x_145 = lean_unbox(x_122);
x_146 = lean_unbox(x_144);
x_147 = l_Lean_Meta_mkLambdaFVars(x_143, x_2, x_121, x_145, x_121, x_146, x_3, x_4, x_5, x_6, x_140);
lean_dec(x_143);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = lean_mk_string_unchecked("instCompleteLatticePi", 21, 21);
x_151 = l_Lean_Name_mkStr3(x_117, x_118, x_150);
x_152 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_152, 0, x_139);
x_153 = lean_box(0);
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_148);
x_155 = lean_unsigned_to_nat(3u);
x_156 = lean_mk_empty_array_with_capacity(x_155);
x_157 = lean_array_push(x_156, x_152);
x_158 = lean_array_push(x_157, x_153);
x_159 = lean_array_push(x_158, x_154);
x_160 = l_Lean_Meta_mkAppOptM(x_151, x_159, x_3, x_4, x_5, x_6, x_149);
return x_160;
}
else
{
lean_dec(x_139);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_147;
}
}
else
{
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_138;
}
}
}
else
{
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_123;
}
}
else
{
lean_object* x_161; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_161 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_116);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; uint8_t x_170; uint8_t x_171; uint8_t x_172; lean_object* x_173; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = lean_unsigned_to_nat(1u);
x_165 = lean_mk_empty_array_with_capacity(x_164);
x_166 = lean_array_push(x_165, x_1);
x_167 = lean_box(0);
x_168 = lean_box(1);
x_169 = lean_unbox(x_167);
x_170 = lean_unbox(x_122);
x_171 = lean_unbox(x_167);
x_172 = lean_unbox(x_168);
x_173 = l_Lean_Meta_mkLambdaFVars(x_166, x_2, x_169, x_170, x_171, x_172, x_3, x_4, x_5, x_6, x_163);
lean_dec(x_166);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_176 = lean_mk_string_unchecked("instCCPOPi", 10, 10);
x_177 = l_Lean_Name_mkStr3(x_117, x_118, x_176);
x_178 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_178, 0, x_162);
x_179 = lean_box(0);
x_180 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_180, 0, x_174);
x_181 = lean_unsigned_to_nat(3u);
x_182 = lean_mk_empty_array_with_capacity(x_181);
x_183 = lean_array_push(x_182, x_178);
x_184 = lean_array_push(x_183, x_179);
x_185 = lean_array_push(x_184, x_180);
x_186 = l_Lean_Meta_mkAppOptM(x_177, x_185, x_3, x_4, x_5, x_6, x_175);
return x_186;
}
else
{
lean_dec(x_162);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_173;
}
}
else
{
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_161;
}
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFixOfMonFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_9 = lean_infer_type(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_mk_string_unchecked("Lean", 4, 4);
x_14 = lean_mk_string_unchecked("Order", 5, 5);
x_15 = lean_mk_string_unchecked("CCPO", 4, 4);
lean_inc(x_14);
lean_inc(x_13);
x_16 = l_Lean_Name_mkStr3(x_13, x_14, x_15);
x_17 = l_Lean_Expr_isAppOf(x_11, x_16);
lean_dec(x_16);
lean_dec(x_11);
if (x_17 == 0)
{
lean_object* x_18; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_18 = lean_infer_type(x_2, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_mk_string_unchecked("CompleteLattice", 15, 15);
lean_inc(x_14);
lean_inc(x_13);
x_23 = l_Lean_Name_mkStr3(x_13, x_14, x_22);
x_24 = l_Lean_Expr_isAppOf(x_20, x_23);
lean_dec(x_23);
lean_dec(x_20);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_1);
x_25 = lean_mk_string_unchecked("mkFixOfMonFun: unexpected type of ", 34, 34);
x_26 = l_Lean_stringToMessageData(x_25);
lean_dec(x_25);
x_27 = l_Lean_MessageData_ofExpr(x_2);
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_27);
lean_ctor_set(x_18, 0, x_26);
x_28 = lean_mk_string_unchecked("", 0, 0);
x_29 = l_Lean_stringToMessageData(x_28);
lean_dec(x_28);
lean_ctor_set_tag(x_9, 7);
lean_ctor_set(x_9, 1, x_29);
lean_ctor_set(x_9, 0, x_18);
x_30 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_9, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_free_object(x_18);
lean_free_object(x_9);
x_31 = lean_mk_string_unchecked("lfp_monotone", 12, 12);
x_32 = l_Lean_Name_mkStr3(x_13, x_14, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_1);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_2);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_3);
x_37 = lean_unsigned_to_nat(4u);
x_38 = lean_mk_empty_array_with_capacity(x_37);
x_39 = lean_array_push(x_38, x_33);
x_40 = lean_array_push(x_39, x_34);
x_41 = lean_array_push(x_40, x_35);
x_42 = lean_array_push(x_41, x_36);
x_43 = l_Lean_Meta_mkAppOptM(x_32, x_42, x_4, x_5, x_6, x_7, x_21);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_44 = lean_ctor_get(x_18, 0);
x_45 = lean_ctor_get(x_18, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_18);
x_46 = lean_mk_string_unchecked("CompleteLattice", 15, 15);
lean_inc(x_14);
lean_inc(x_13);
x_47 = l_Lean_Name_mkStr3(x_13, x_14, x_46);
x_48 = l_Lean_Expr_isAppOf(x_44, x_47);
lean_dec(x_47);
lean_dec(x_44);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_1);
x_49 = lean_mk_string_unchecked("mkFixOfMonFun: unexpected type of ", 34, 34);
x_50 = l_Lean_stringToMessageData(x_49);
lean_dec(x_49);
x_51 = l_Lean_MessageData_ofExpr(x_2);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_mk_string_unchecked("", 0, 0);
x_54 = l_Lean_stringToMessageData(x_53);
lean_dec(x_53);
lean_ctor_set_tag(x_9, 7);
lean_ctor_set(x_9, 1, x_54);
lean_ctor_set(x_9, 0, x_52);
x_55 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_9, x_4, x_5, x_6, x_7, x_45);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_free_object(x_9);
x_56 = lean_mk_string_unchecked("lfp_monotone", 12, 12);
x_57 = l_Lean_Name_mkStr3(x_13, x_14, x_56);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_1);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_2);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_3);
x_62 = lean_unsigned_to_nat(4u);
x_63 = lean_mk_empty_array_with_capacity(x_62);
x_64 = lean_array_push(x_63, x_58);
x_65 = lean_array_push(x_64, x_59);
x_66 = lean_array_push(x_65, x_60);
x_67 = lean_array_push(x_66, x_61);
x_68 = l_Lean_Meta_mkAppOptM(x_57, x_67, x_4, x_5, x_6, x_7, x_45);
return x_68;
}
}
}
else
{
lean_dec(x_14);
lean_dec(x_13);
lean_free_object(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_free_object(x_9);
x_69 = lean_mk_string_unchecked("fix", 3, 3);
x_70 = l_Lean_Name_mkStr3(x_13, x_14, x_69);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_1);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_2);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_3);
x_75 = lean_unsigned_to_nat(4u);
x_76 = lean_mk_empty_array_with_capacity(x_75);
x_77 = lean_array_push(x_76, x_71);
x_78 = lean_array_push(x_77, x_72);
x_79 = lean_array_push(x_78, x_73);
x_80 = lean_array_push(x_79, x_74);
x_81 = l_Lean_Meta_mkAppOptM(x_70, x_80, x_4, x_5, x_6, x_7, x_12);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_82 = lean_ctor_get(x_9, 0);
x_83 = lean_ctor_get(x_9, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_9);
x_84 = lean_mk_string_unchecked("Lean", 4, 4);
x_85 = lean_mk_string_unchecked("Order", 5, 5);
x_86 = lean_mk_string_unchecked("CCPO", 4, 4);
lean_inc(x_85);
lean_inc(x_84);
x_87 = l_Lean_Name_mkStr3(x_84, x_85, x_86);
x_88 = l_Lean_Expr_isAppOf(x_82, x_87);
lean_dec(x_87);
lean_dec(x_82);
if (x_88 == 0)
{
lean_object* x_89; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_89 = lean_infer_type(x_2, x_4, x_5, x_6, x_7, x_83);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_92 = x_89;
} else {
 lean_dec_ref(x_89);
 x_92 = lean_box(0);
}
x_93 = lean_mk_string_unchecked("CompleteLattice", 15, 15);
lean_inc(x_85);
lean_inc(x_84);
x_94 = l_Lean_Name_mkStr3(x_84, x_85, x_93);
x_95 = l_Lean_Expr_isAppOf(x_90, x_94);
lean_dec(x_94);
lean_dec(x_90);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_3);
lean_dec(x_1);
x_96 = lean_mk_string_unchecked("mkFixOfMonFun: unexpected type of ", 34, 34);
x_97 = l_Lean_stringToMessageData(x_96);
lean_dec(x_96);
x_98 = l_Lean_MessageData_ofExpr(x_2);
if (lean_is_scalar(x_92)) {
 x_99 = lean_alloc_ctor(7, 2, 0);
} else {
 x_99 = x_92;
 lean_ctor_set_tag(x_99, 7);
}
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_mk_string_unchecked("", 0, 0);
x_101 = l_Lean_stringToMessageData(x_100);
lean_dec(x_100);
x_102 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_102, x_4, x_5, x_6, x_7, x_91);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_92);
x_104 = lean_mk_string_unchecked("lfp_monotone", 12, 12);
x_105 = l_Lean_Name_mkStr3(x_84, x_85, x_104);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_1);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_2);
x_108 = lean_box(0);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_3);
x_110 = lean_unsigned_to_nat(4u);
x_111 = lean_mk_empty_array_with_capacity(x_110);
x_112 = lean_array_push(x_111, x_106);
x_113 = lean_array_push(x_112, x_107);
x_114 = lean_array_push(x_113, x_108);
x_115 = lean_array_push(x_114, x_109);
x_116 = l_Lean_Meta_mkAppOptM(x_105, x_115, x_4, x_5, x_6, x_7, x_91);
return x_116;
}
}
else
{
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_89;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_117 = lean_mk_string_unchecked("fix", 3, 3);
x_118 = l_Lean_Name_mkStr3(x_84, x_85, x_117);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_1);
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_2);
x_121 = lean_box(0);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_3);
x_123 = lean_unsigned_to_nat(4u);
x_124 = lean_mk_empty_array_with_capacity(x_123);
x_125 = lean_array_push(x_124, x_119);
x_126 = lean_array_push(x_125, x_120);
x_127 = lean_array_push(x_126, x_121);
x_128 = lean_array_push(x_127, x_122);
x_129 = l_Lean_Meta_mkAppOptM(x_118, x_128, x_4, x_5, x_6, x_7, x_83);
return x_129;
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
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_toPartialOrder(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_mk_string_unchecked("Lean", 4, 4);
x_13 = lean_mk_string_unchecked("Order", 5, 5);
x_14 = lean_mk_string_unchecked("CCPO", 4, 4);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_15 = l_Lean_Name_mkStr3(x_12, x_13, x_14);
x_16 = l_Lean_Expr_isAppOf(x_10, x_15);
lean_dec(x_15);
lean_dec(x_10);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_17 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_mk_string_unchecked("CompleteLattice", 15, 15);
lean_inc(x_21);
lean_inc(x_13);
lean_inc(x_12);
x_22 = l_Lean_Name_mkStr3(x_12, x_13, x_21);
x_23 = l_Lean_Expr_isAppOf(x_19, x_22);
lean_dec(x_22);
lean_dec(x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_21);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_2);
x_24 = lean_mk_string_unchecked("getUnderlyingOrder: unexpected type of ", 39, 39);
x_25 = l_Lean_stringToMessageData(x_24);
lean_dec(x_24);
x_26 = l_Lean_MessageData_ofExpr(x_1);
lean_ctor_set_tag(x_17, 7);
lean_ctor_set(x_17, 1, x_26);
lean_ctor_set(x_17, 0, x_25);
x_27 = lean_mk_string_unchecked("", 0, 0);
x_28 = l_Lean_stringToMessageData(x_27);
lean_dec(x_27);
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_28);
lean_ctor_set(x_8, 0, x_17);
x_29 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_8, x_3, x_4, x_5, x_6, x_20);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_free_object(x_17);
lean_free_object(x_8);
x_30 = lean_mk_string_unchecked("toPartialOrder", 14, 14);
x_31 = l_Lean_Name_mkStr4(x_12, x_13, x_21, x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_1);
x_33 = lean_unsigned_to_nat(2u);
x_34 = lean_mk_empty_array_with_capacity(x_33);
x_35 = lean_array_push(x_34, x_2);
x_36 = lean_array_push(x_35, x_32);
x_37 = l_Lean_Meta_mkAppOptM(x_31, x_36, x_3, x_4, x_5, x_6, x_20);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_38 = lean_ctor_get(x_17, 0);
x_39 = lean_ctor_get(x_17, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_17);
x_40 = lean_mk_string_unchecked("CompleteLattice", 15, 15);
lean_inc(x_40);
lean_inc(x_13);
lean_inc(x_12);
x_41 = l_Lean_Name_mkStr3(x_12, x_13, x_40);
x_42 = l_Lean_Expr_isAppOf(x_38, x_41);
lean_dec(x_41);
lean_dec(x_38);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_40);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_2);
x_43 = lean_mk_string_unchecked("getUnderlyingOrder: unexpected type of ", 39, 39);
x_44 = l_Lean_stringToMessageData(x_43);
lean_dec(x_43);
x_45 = l_Lean_MessageData_ofExpr(x_1);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_mk_string_unchecked("", 0, 0);
x_48 = l_Lean_stringToMessageData(x_47);
lean_dec(x_47);
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_48);
lean_ctor_set(x_8, 0, x_46);
x_49 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_8, x_3, x_4, x_5, x_6, x_39);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_free_object(x_8);
x_50 = lean_mk_string_unchecked("toPartialOrder", 14, 14);
x_51 = l_Lean_Name_mkStr4(x_12, x_13, x_40, x_50);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_1);
x_53 = lean_unsigned_to_nat(2u);
x_54 = lean_mk_empty_array_with_capacity(x_53);
x_55 = lean_array_push(x_54, x_2);
x_56 = lean_array_push(x_55, x_52);
x_57 = l_Lean_Meta_mkAppOptM(x_51, x_56, x_3, x_4, x_5, x_6, x_39);
return x_57;
}
}
}
else
{
lean_dec(x_13);
lean_dec(x_12);
lean_free_object(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_free_object(x_8);
x_58 = lean_mk_string_unchecked("toPartialOrder", 14, 14);
x_59 = l_Lean_Name_mkStr4(x_12, x_13, x_14, x_58);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_1);
x_61 = lean_unsigned_to_nat(2u);
x_62 = lean_mk_empty_array_with_capacity(x_61);
x_63 = lean_array_push(x_62, x_2);
x_64 = lean_array_push(x_63, x_60);
x_65 = l_Lean_Meta_mkAppOptM(x_59, x_64, x_3, x_4, x_5, x_6, x_11);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_66 = lean_ctor_get(x_8, 0);
x_67 = lean_ctor_get(x_8, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_8);
x_68 = lean_mk_string_unchecked("Lean", 4, 4);
x_69 = lean_mk_string_unchecked("Order", 5, 5);
x_70 = lean_mk_string_unchecked("CCPO", 4, 4);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
x_71 = l_Lean_Name_mkStr3(x_68, x_69, x_70);
x_72 = l_Lean_Expr_isAppOf(x_66, x_71);
lean_dec(x_71);
lean_dec(x_66);
if (x_72 == 0)
{
lean_object* x_73; 
lean_dec(x_70);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_73 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_67);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_76 = x_73;
} else {
 lean_dec_ref(x_73);
 x_76 = lean_box(0);
}
x_77 = lean_mk_string_unchecked("CompleteLattice", 15, 15);
lean_inc(x_77);
lean_inc(x_69);
lean_inc(x_68);
x_78 = l_Lean_Name_mkStr3(x_68, x_69, x_77);
x_79 = l_Lean_Expr_isAppOf(x_74, x_78);
lean_dec(x_78);
lean_dec(x_74);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_77);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_2);
x_80 = lean_mk_string_unchecked("getUnderlyingOrder: unexpected type of ", 39, 39);
x_81 = l_Lean_stringToMessageData(x_80);
lean_dec(x_80);
x_82 = l_Lean_MessageData_ofExpr(x_1);
if (lean_is_scalar(x_76)) {
 x_83 = lean_alloc_ctor(7, 2, 0);
} else {
 x_83 = x_76;
 lean_ctor_set_tag(x_83, 7);
}
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_mk_string_unchecked("", 0, 0);
x_85 = l_Lean_stringToMessageData(x_84);
lean_dec(x_84);
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_86, x_3, x_4, x_5, x_6, x_75);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_76);
x_88 = lean_mk_string_unchecked("toPartialOrder", 14, 14);
x_89 = l_Lean_Name_mkStr4(x_68, x_69, x_77, x_88);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_1);
x_91 = lean_unsigned_to_nat(2u);
x_92 = lean_mk_empty_array_with_capacity(x_91);
x_93 = lean_array_push(x_92, x_2);
x_94 = lean_array_push(x_93, x_90);
x_95 = l_Lean_Meta_mkAppOptM(x_89, x_94, x_3, x_4, x_5, x_6, x_75);
return x_95;
}
}
else
{
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_73;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_96 = lean_mk_string_unchecked("toPartialOrder", 14, 14);
x_97 = l_Lean_Name_mkStr4(x_68, x_69, x_70, x_96);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_1);
x_99 = lean_unsigned_to_nat(2u);
x_100 = lean_mk_empty_array_with_capacity(x_99);
x_101 = lean_array_push(x_100, x_2);
x_102 = lean_array_push(x_101, x_98);
x_103 = l_Lean_Meta_mkAppOptM(x_97, x_102, x_3, x_4, x_5, x_6, x_67);
return x_103;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInstCCPOPProd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_8 = lean_mk_string_unchecked("Lean", 4, 4);
x_9 = lean_mk_string_unchecked("Order", 5, 5);
x_10 = lean_mk_string_unchecked("instCCPOPProd", 13, 13);
x_11 = l_Lean_Name_mkStr3(x_8, x_9, x_10);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_1);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_2);
x_15 = lean_unsigned_to_nat(4u);
x_16 = lean_mk_empty_array_with_capacity(x_15);
x_17 = lean_array_push(x_16, x_12);
x_18 = lean_array_push(x_17, x_12);
x_19 = lean_array_push(x_18, x_13);
x_20 = lean_array_push(x_19, x_14);
x_21 = l_Lean_Meta_mkAppOptM(x_11, x_20, x_3, x_4, x_5, x_6, x_7);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInstCompleteLatticePProd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_8 = lean_mk_string_unchecked("Lean", 4, 4);
x_9 = lean_mk_string_unchecked("Order", 5, 5);
x_10 = lean_mk_string_unchecked("instCompleteLatticePProd", 24, 24);
x_11 = l_Lean_Name_mkStr3(x_8, x_9, x_10);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_1);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_2);
x_15 = lean_unsigned_to_nat(4u);
x_16 = lean_mk_empty_array_with_capacity(x_15);
x_17 = lean_array_push(x_16, x_12);
x_18 = lean_array_push(x_17, x_12);
x_19 = lean_array_push(x_18, x_13);
x_20 = lean_array_push(x_19, x_14);
x_21 = l_Lean_Meta_mkAppOptM(x_11, x_20, x_3, x_4, x_5, x_6, x_7);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_mkPackedPPRodInstance_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_2, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget(x_3, x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_12 = lean_infer_type(x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = lean_array_uset(x_3, x_2, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_usize_of_nat(x_17);
x_19 = lean_usize_add(x_2, x_18);
x_20 = lean_array_uset(x_16, x_2, x_13);
x_2 = x_19;
x_3 = x_20;
x_8 = x_14;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Meta_mkPackedPPRodInstance_spec__1(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_box(1);
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Order", 5, 5);
x_9 = lean_mk_string_unchecked("CCPO", 4, 4);
x_10 = l_Lean_Name_mkStr3(x_7, x_8, x_9);
x_11 = l_Lean_Expr_isAppOf(x_6, x_10);
lean_dec(x_10);
lean_dec(x_6);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = lean_unbox(x_5);
return x_12;
}
else
{
if (x_4 == 0)
{
lean_object* x_13; size_t x_14; size_t x_15; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_usize_of_nat(x_13);
x_15 = lean_usize_add(x_2, x_14);
x_2 = x_15;
goto _start;
}
else
{
uint8_t x_17; 
x_17 = lean_unbox(x_5);
return x_17;
}
}
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_box(0);
x_19 = lean_unbox(x_18);
return x_19;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Meta_mkPackedPPRodInstance_spec__2(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_3, x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_array_uget(x_2, x_3);
x_12 = lean_mk_string_unchecked("Lean", 4, 4);
x_13 = lean_mk_string_unchecked("Order", 5, 5);
x_14 = lean_mk_string_unchecked("CompleteLattice", 15, 15);
x_15 = l_Lean_Name_mkStr3(x_12, x_13, x_14);
x_16 = l_Lean_Expr_isAppOf(x_11, x_15);
lean_dec(x_15);
lean_dec(x_11);
if (x_16 == 0)
{
if (x_1 == 0)
{
goto block_9;
}
else
{
return x_1;
}
}
else
{
goto block_9;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
return x_18;
}
block_9:
{
lean_object* x_5; size_t x_6; size_t x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_usize_of_nat(x_5);
x_7 = lean_usize_add(x_3, x_6);
x_3 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPackedPPRodInstance(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_array_size(x_1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_usize_of_nat(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Array_mapMUnsafe_map___at___Lean_Meta_mkPackedPPRodInstance_spec__0(x_7, x_9, x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_21; uint8_t x_22; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_21 = lean_array_get_size(x_11);
x_22 = lean_nat_dec_lt(x_8, x_21);
if (x_22 == 0)
{
lean_dec(x_21);
lean_dec(x_11);
goto block_20;
}
else
{
if (x_22 == 0)
{
lean_dec(x_21);
lean_dec(x_11);
goto block_20;
}
else
{
size_t x_23; uint8_t x_24; 
x_23 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_24 = l_Array_anyMUnsafe_any___at___Lean_Meta_mkPackedPPRodInstance_spec__1(x_11, x_9, x_23);
if (x_24 == 0)
{
lean_dec(x_11);
goto block_20;
}
else
{
if (x_22 == 0)
{
lean_dec(x_11);
goto block_16;
}
else
{
if (x_22 == 0)
{
lean_dec(x_11);
goto block_16;
}
else
{
uint8_t x_25; 
x_25 = l_Array_anyMUnsafe_any___at___Lean_Meta_mkPackedPPRodInstance_spec__2(x_24, x_11, x_9, x_23);
if (x_25 == 0)
{
lean_dec(x_11);
goto block_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_26 = lean_mk_string_unchecked("mkPackedPPRoodInstance: unexpected types ", 41, 41);
x_27 = l_Lean_stringToMessageData(x_26);
lean_dec(x_26);
x_28 = lean_array_to_list(x_11);
x_29 = lean_box(0);
x_30 = l_List_mapTR_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0_spec__0(x_28, x_29);
x_31 = l_Lean_MessageData_ofList(x_30);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_mk_string_unchecked(" of ", 4, 4);
x_34 = l_Lean_stringToMessageData(x_33);
lean_dec(x_33);
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_array_to_list(x_1);
x_37 = l_List_mapTR_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0_spec__0(x_36, x_29);
x_38 = l_Lean_MessageData_ofList(x_37);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_mk_string_unchecked("", 0, 0);
x_41 = l_Lean_stringToMessageData(x_40);
lean_dec(x_40);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_42, x_2, x_3, x_4, x_5, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_43;
}
}
}
}
}
}
block_16:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_Lean_instInhabitedExpr;
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_mkInstCompleteLatticePProd), 7, 0);
x_15 = l_Lean_Meta_PProdN_genMk___redArg(x_13, x_14, x_1, x_2, x_3, x_4, x_5, x_12);
return x_15;
}
block_20:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = l_Lean_instInhabitedExpr;
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_mkInstCCPOPProd), 7, 0);
x_19 = l_Lean_Meta_PProdN_genMk___redArg(x_17, x_18, x_1, x_2, x_3, x_4, x_5, x_12);
return x_19;
}
}
else
{
uint8_t x_44; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_10);
if (x_44 == 0)
{
return x_10;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_10, 0);
x_46 = lean_ctor_get(x_10, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_10);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_mkPackedPPRodInstance_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at___Lean_Meta_mkPackedPPRodInstance_spec__0(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Meta_mkPackedPPRodInstance_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___Lean_Meta_mkPackedPPRodInstance_spec__1(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Meta_mkPackedPPRodInstance_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_anyMUnsafe_any___at___Lean_Meta_mkPackedPPRodInstance_spec__2(x_5, x_2, x_6, x_7);
lean_dec(x_2);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* initialize_Lean_Meta_InferType(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_PProdN(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Internal_Order_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Order(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_InferType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_PProdN(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Internal_Order_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
