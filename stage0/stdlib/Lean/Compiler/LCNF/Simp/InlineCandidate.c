// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.InlineCandidate
// Imports: Lean.Compiler.LCNF.Simp.SimpM
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity___boxed(lean_object*);
uint8_t l_Lean_Compiler_LCNF_Decl_noinlineAttr(lean_object*);
uint8_t l_Lean_Compiler_LCNF_Decl_alwaysInlineAttr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_isInstance___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_initFn____x40_Lean_Compiler_LCNF_Simp_InlineCandidate___hyg_1361_(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_instantiateTypeLevelParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_getArity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__1(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Arg_isConstructorApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Decl_inlineAttr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_inBasePhase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Decl_inlineIfReduceAttr(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isSmall___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_incInline(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_isCasesOnParam_x3f(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDecl_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_array_get_size(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_22; 
x_22 = l_Lean_Compiler_LCNF_Decl_alwaysInlineAttr(x_1);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = l_Lean_Compiler_LCNF_Decl_inlineAttr(x_1);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_Lean_Compiler_LCNF_Decl_inlineIfReduceAttr(x_1);
x_14 = x_24;
goto block_21;
}
else
{
x_14 = x_23;
goto block_21;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(x_4);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_13);
return x_26;
}
block_21:
{
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = l_Lean_Compiler_LCNF_Decl_noinlineAttr(x_1);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = l_Lean_Compiler_LCNF_Simp_isSmall___redArg(x_2, x_9, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(x_3);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(x_4);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_13);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__1(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_5, 1);
x_18 = lean_ctor_get_uint8(x_17, 3);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_12);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 2);
lean_inc(x_23);
lean_dec(x_2);
x_24 = l_Lean_Compiler_LCNF_getDecl_x3f___redArg(x_21, x_8, x_11, x_12);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_23);
lean_dec(x_22);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_25, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_33 = x_25;
} else {
 lean_dec_ref(x_25);
 x_33 = lean_box(0);
}
x_34 = lean_ctor_get(x_32, 4);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_67; lean_object* x_68; uint8_t x_90; uint8_t x_91; lean_object* x_92; uint8_t x_100; lean_object* x_101; uint8_t x_106; lean_object* x_107; uint8_t x_121; uint8_t x_122; uint8_t x_130; 
x_35 = lean_ctor_get(x_24, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_36 = x_24;
} else {
 lean_dec_ref(x_24);
 x_36 = lean_box(0);
}
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
lean_dec(x_34);
x_38 = l_Lean_Compiler_LCNF_Decl_inlineIfReduceAttr(x_32);
if (x_38 == 0)
{
if (x_18 == 0)
{
goto block_134;
}
else
{
uint8_t x_135; 
x_135 = lean_ctor_get_uint8(x_32, sizeof(void*)*6);
if (x_135 == 0)
{
goto block_134;
}
else
{
x_130 = x_18;
goto block_131;
}
}
}
else
{
goto block_134;
}
block_66:
{
lean_object* x_47; uint8_t x_48; 
x_47 = l_Lean_Compiler_LCNF_Simp_incInline(x_39, x_40, x_41, x_42, x_43, x_44, x_45, x_46);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
x_50 = lean_ctor_get(x_32, 1);
lean_inc(x_50);
lean_inc(x_22);
lean_inc(x_32);
x_51 = l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams(x_32, x_22);
lean_inc(x_22);
x_52 = l_Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode(x_50, x_22, x_37);
lean_inc(x_32);
x_53 = l_Lean_Compiler_LCNF_Decl_instantiateTypeLevelParams(x_32, x_22);
x_54 = lean_ctor_get_uint8(x_32, sizeof(void*)*6);
lean_dec(x_32);
x_55 = lean_alloc_ctor(0, 4, 3);
lean_ctor_set(x_55, 0, x_51);
lean_ctor_set(x_55, 1, x_52);
lean_ctor_set(x_55, 2, x_53);
lean_ctor_set(x_55, 3, x_23);
lean_ctor_set_uint8(x_55, sizeof(void*)*4, x_1);
lean_ctor_set_uint8(x_55, sizeof(void*)*4 + 1, x_38);
lean_ctor_set_uint8(x_55, sizeof(void*)*4 + 2, x_54);
if (lean_is_scalar(x_33)) {
 x_56 = lean_alloc_ctor(1, 1, 0);
} else {
 x_56 = x_33;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_47, 0, x_56);
return x_47;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_57 = lean_ctor_get(x_47, 1);
lean_inc(x_57);
lean_dec(x_47);
x_58 = lean_ctor_get(x_32, 1);
lean_inc(x_58);
lean_inc(x_22);
lean_inc(x_32);
x_59 = l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams(x_32, x_22);
lean_inc(x_22);
x_60 = l_Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode(x_58, x_22, x_37);
lean_inc(x_32);
x_61 = l_Lean_Compiler_LCNF_Decl_instantiateTypeLevelParams(x_32, x_22);
x_62 = lean_ctor_get_uint8(x_32, sizeof(void*)*6);
lean_dec(x_32);
x_63 = lean_alloc_ctor(0, 4, 3);
lean_ctor_set(x_63, 0, x_59);
lean_ctor_set(x_63, 1, x_60);
lean_ctor_set(x_63, 2, x_61);
lean_ctor_set(x_63, 3, x_23);
lean_ctor_set_uint8(x_63, sizeof(void*)*4, x_1);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 1, x_38);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 2, x_62);
if (lean_is_scalar(x_33)) {
 x_64 = lean_alloc_ctor(1, 1, 0);
} else {
 x_64 = x_33;
}
lean_ctor_set(x_64, 0, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_57);
return x_65;
}
}
block_89:
{
if (x_67 == 0)
{
lean_dec(x_36);
x_39 = x_5;
x_40 = x_6;
x_41 = x_7;
x_42 = x_8;
x_43 = x_9;
x_44 = x_10;
x_45 = x_11;
x_46 = x_68;
goto block_66;
}
else
{
lean_object* x_69; 
lean_inc(x_32);
x_69 = l_Lean_Compiler_LCNF_Decl_isCasesOnParam_x3f(x_32);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_23);
lean_dec(x_22);
x_70 = lean_box(0);
if (lean_is_scalar(x_36)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_36;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_68);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_ctor_get(x_69, 0);
lean_inc(x_72);
lean_dec(x_69);
x_73 = lean_array_get_size(x_23);
x_74 = lean_nat_dec_lt(x_72, x_73);
lean_dec(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_72);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_23);
lean_dec(x_22);
x_75 = lean_box(0);
if (lean_is_scalar(x_36)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_36;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_68);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
lean_dec(x_36);
x_77 = lean_box(0);
x_78 = lean_array_get(x_77, x_23, x_72);
lean_dec(x_72);
x_79 = l_Lean_Compiler_LCNF_Arg_isConstructorApp(x_78, x_8, x_9, x_10, x_11, x_68);
lean_dec(x_78);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
if (x_81 == 0)
{
uint8_t x_82; 
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_23);
lean_dec(x_22);
x_82 = !lean_is_exclusive(x_79);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_79, 0);
lean_dec(x_83);
x_84 = lean_box(0);
lean_ctor_set(x_79, 0, x_84);
return x_79;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_79, 1);
lean_inc(x_85);
lean_dec(x_79);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
else
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_79, 1);
lean_inc(x_88);
lean_dec(x_79);
x_39 = x_5;
x_40 = x_6;
x_41 = x_7;
x_42 = x_8;
x_43 = x_9;
x_44 = x_10;
x_45 = x_11;
x_46 = x_88;
goto block_66;
}
}
}
}
}
block_99:
{
if (x_91 == 0)
{
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_23);
lean_dec(x_22);
x_13 = x_92;
goto block_16;
}
else
{
if (x_3 == 0)
{
uint8_t x_93; 
x_93 = lean_ctor_get_uint8(x_17, 1);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_94 = l_Lean_Compiler_LCNF_Decl_getArity(x_32);
x_95 = lean_array_get_size(x_23);
x_96 = lean_nat_dec_lt(x_95, x_94);
lean_dec(x_94);
lean_dec(x_95);
if (x_96 == 0)
{
x_67 = x_90;
x_68 = x_92;
goto block_89;
}
else
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_23);
lean_dec(x_22);
x_97 = lean_box(0);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_92);
return x_98;
}
}
else
{
x_67 = x_90;
x_68 = x_92;
goto block_89;
}
}
else
{
x_67 = x_90;
x_68 = x_92;
goto block_89;
}
}
}
block_105:
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_unbox(x_102);
lean_dec(x_102);
x_90 = x_100;
x_91 = x_104;
x_92 = x_103;
goto block_99;
}
block_120:
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_unbox(x_108);
lean_dec(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_107, 1);
lean_inc(x_110);
lean_dec(x_107);
x_111 = lean_box(0);
x_112 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__0(x_32, x_37, x_1, x_18, x_111, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_110);
x_100 = x_106;
x_101 = x_112;
goto block_105;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_113 = lean_ctor_get(x_107, 1);
lean_inc(x_113);
lean_dec(x_107);
x_114 = lean_ctor_get(x_32, 0);
lean_inc(x_114);
x_115 = lean_mk_string_unchecked("instDecidableEqBool", 19, 19);
x_116 = l_Lean_Name_mkStr1(x_115);
x_117 = lean_name_eq(x_114, x_116);
lean_dec(x_116);
lean_dec(x_114);
if (x_117 == 0)
{
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_23);
lean_dec(x_22);
x_13 = x_113;
goto block_16;
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_box(0);
x_119 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__0(x_32, x_37, x_1, x_18, x_118, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_113);
x_100 = x_106;
x_101 = x_119;
goto block_105;
}
}
}
block_129:
{
if (x_121 == 0)
{
if (x_3 == 0)
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_123 = l_Lean_Compiler_LCNF_inBasePhase(x_8, x_9, x_10, x_11, x_35);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_unbox(x_124);
lean_dec(x_124);
if (x_125 == 0)
{
x_106 = x_122;
x_107 = x_123;
goto block_120;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
lean_dec(x_123);
x_127 = lean_ctor_get(x_32, 0);
lean_inc(x_127);
x_128 = l_Lean_Meta_isInstance___redArg(x_127, x_11, x_126);
lean_dec(x_127);
x_106 = x_122;
x_107 = x_128;
goto block_120;
}
}
else
{
x_90 = x_122;
x_91 = x_18;
x_92 = x_35;
goto block_99;
}
}
else
{
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_23);
lean_dec(x_22);
x_13 = x_35;
goto block_16;
}
}
block_131:
{
if (x_38 == 0)
{
x_121 = x_130;
x_122 = x_38;
goto block_129;
}
else
{
x_121 = x_130;
x_122 = x_18;
goto block_129;
}
}
block_134:
{
lean_object* x_132; uint8_t x_133; 
x_132 = lean_box(0);
x_133 = lean_unbox(x_132);
x_130 = x_133;
goto block_131;
}
}
else
{
uint8_t x_136; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_23);
lean_dec(x_22);
x_136 = !lean_is_exclusive(x_24);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_24, 0);
lean_dec(x_137);
x_138 = lean_box(0);
lean_ctor_set(x_24, 0, x_138);
return x_24;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_24, 1);
lean_inc(x_139);
lean_dec(x_24);
x_140 = lean_box(0);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_139);
return x_141;
}
}
}
}
}
else
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_142 = lean_ctor_get(x_2, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_2, 1);
lean_inc(x_143);
lean_dec(x_2);
lean_inc(x_142);
x_144 = l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f(x_142, x_8, x_9, x_10, x_11, x_12);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
if (lean_obj_tag(x_145) == 0)
{
uint8_t x_146; 
lean_dec(x_143);
lean_dec(x_142);
x_146 = !lean_is_exclusive(x_144);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_144, 0);
lean_dec(x_147);
x_148 = lean_box(0);
lean_ctor_set(x_144, 0, x_148);
return x_144;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_144, 1);
lean_inc(x_149);
lean_dec(x_144);
x_150 = lean_box(0);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
}
else
{
uint8_t x_152; 
x_152 = !lean_is_exclusive(x_144);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_153 = lean_ctor_get(x_144, 1);
x_154 = lean_ctor_get(x_144, 0);
lean_dec(x_154);
x_155 = lean_ctor_get(x_145, 0);
lean_inc(x_155);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 x_156 = x_145;
} else {
 lean_dec_ref(x_145);
 x_156 = lean_box(0);
}
x_157 = lean_unsigned_to_nat(0u);
x_158 = lean_array_get_size(x_143);
x_159 = lean_nat_dec_lt(x_157, x_158);
lean_dec(x_158);
if (x_159 == 0)
{
lean_object* x_160; 
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_143);
lean_dec(x_142);
x_160 = lean_box(0);
lean_ctor_set(x_144, 0, x_160);
return x_144;
}
else
{
lean_object* x_161; uint8_t x_162; 
lean_free_object(x_144);
x_161 = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(x_155, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_153);
x_162 = !lean_is_exclusive(x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_163 = lean_ctor_get(x_161, 0);
x_164 = lean_ctor_get(x_161, 1);
if (x_3 == 0)
{
uint8_t x_203; 
x_203 = lean_unbox(x_163);
if (x_203 == 0)
{
lean_object* x_204; 
lean_dec(x_163);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_143);
lean_dec(x_142);
x_204 = lean_box(0);
lean_ctor_set(x_161, 0, x_204);
return x_161;
}
else
{
uint8_t x_205; 
lean_free_object(x_161);
x_205 = lean_unbox(x_163);
lean_dec(x_163);
x_165 = x_205;
goto block_202;
}
}
else
{
lean_free_object(x_161);
lean_dec(x_163);
x_165 = x_3;
goto block_202;
}
block_202:
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_166 = l_Lean_Compiler_LCNF_Simp_incInlineLocal(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_164);
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
lean_dec(x_166);
x_168 = lean_st_ref_take(x_6, x_167);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
x_171 = lean_ctor_get(x_169, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_169, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_169, 2);
lean_inc(x_173);
x_174 = lean_ctor_get(x_169, 3);
lean_inc(x_174);
x_175 = lean_ctor_get_uint8(x_169, sizeof(void*)*7);
x_176 = lean_ctor_get(x_169, 4);
lean_inc(x_176);
x_177 = lean_ctor_get(x_169, 5);
lean_inc(x_177);
x_178 = lean_ctor_get(x_169, 6);
lean_inc(x_178);
lean_dec(x_169);
x_179 = lean_unsigned_to_nat(1u);
x_180 = lean_nat_add(x_178, x_179);
lean_dec(x_178);
x_181 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_181, 0, x_171);
lean_ctor_set(x_181, 1, x_172);
lean_ctor_set(x_181, 2, x_173);
lean_ctor_set(x_181, 3, x_174);
lean_ctor_set(x_181, 4, x_176);
lean_ctor_set(x_181, 5, x_177);
lean_ctor_set(x_181, 6, x_180);
lean_ctor_set_uint8(x_181, sizeof(void*)*7, x_175);
x_182 = lean_st_ref_set(x_6, x_181, x_170);
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
lean_dec(x_182);
x_184 = l_Lean_Compiler_LCNF_getType(x_142, x_8, x_9, x_10, x_11, x_183);
if (lean_obj_tag(x_184) == 0)
{
uint8_t x_185; 
x_185 = !lean_is_exclusive(x_184);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_186 = lean_ctor_get(x_184, 0);
x_187 = lean_ctor_get(x_155, 2);
lean_inc(x_187);
x_188 = lean_ctor_get(x_155, 4);
lean_inc(x_188);
lean_dec(x_155);
x_189 = lean_alloc_ctor(0, 4, 3);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
lean_ctor_set(x_189, 2, x_186);
lean_ctor_set(x_189, 3, x_143);
lean_ctor_set_uint8(x_189, sizeof(void*)*4, x_165);
lean_ctor_set_uint8(x_189, sizeof(void*)*4 + 1, x_1);
lean_ctor_set_uint8(x_189, sizeof(void*)*4 + 2, x_1);
if (lean_is_scalar(x_156)) {
 x_190 = lean_alloc_ctor(1, 1, 0);
} else {
 x_190 = x_156;
}
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_184, 0, x_190);
return x_184;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_191 = lean_ctor_get(x_184, 0);
x_192 = lean_ctor_get(x_184, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_184);
x_193 = lean_ctor_get(x_155, 2);
lean_inc(x_193);
x_194 = lean_ctor_get(x_155, 4);
lean_inc(x_194);
lean_dec(x_155);
x_195 = lean_alloc_ctor(0, 4, 3);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
lean_ctor_set(x_195, 2, x_191);
lean_ctor_set(x_195, 3, x_143);
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_165);
lean_ctor_set_uint8(x_195, sizeof(void*)*4 + 1, x_1);
lean_ctor_set_uint8(x_195, sizeof(void*)*4 + 2, x_1);
if (lean_is_scalar(x_156)) {
 x_196 = lean_alloc_ctor(1, 1, 0);
} else {
 x_196 = x_156;
}
lean_ctor_set(x_196, 0, x_195);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_192);
return x_197;
}
}
else
{
uint8_t x_198; 
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_143);
x_198 = !lean_is_exclusive(x_184);
if (x_198 == 0)
{
return x_184;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_184, 0);
x_200 = lean_ctor_get(x_184, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_184);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
}
else
{
lean_object* x_206; lean_object* x_207; uint8_t x_208; 
x_206 = lean_ctor_get(x_161, 0);
x_207 = lean_ctor_get(x_161, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_161);
if (x_3 == 0)
{
uint8_t x_241; 
x_241 = lean_unbox(x_206);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; 
lean_dec(x_206);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_143);
lean_dec(x_142);
x_242 = lean_box(0);
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_207);
return x_243;
}
else
{
uint8_t x_244; 
x_244 = lean_unbox(x_206);
lean_dec(x_206);
x_208 = x_244;
goto block_240;
}
}
else
{
lean_dec(x_206);
x_208 = x_3;
goto block_240;
}
block_240:
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_209 = l_Lean_Compiler_LCNF_Simp_incInlineLocal(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_207);
x_210 = lean_ctor_get(x_209, 1);
lean_inc(x_210);
lean_dec(x_209);
x_211 = lean_st_ref_take(x_6, x_210);
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
lean_dec(x_211);
x_214 = lean_ctor_get(x_212, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_212, 1);
lean_inc(x_215);
x_216 = lean_ctor_get(x_212, 2);
lean_inc(x_216);
x_217 = lean_ctor_get(x_212, 3);
lean_inc(x_217);
x_218 = lean_ctor_get_uint8(x_212, sizeof(void*)*7);
x_219 = lean_ctor_get(x_212, 4);
lean_inc(x_219);
x_220 = lean_ctor_get(x_212, 5);
lean_inc(x_220);
x_221 = lean_ctor_get(x_212, 6);
lean_inc(x_221);
lean_dec(x_212);
x_222 = lean_unsigned_to_nat(1u);
x_223 = lean_nat_add(x_221, x_222);
lean_dec(x_221);
x_224 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_224, 0, x_214);
lean_ctor_set(x_224, 1, x_215);
lean_ctor_set(x_224, 2, x_216);
lean_ctor_set(x_224, 3, x_217);
lean_ctor_set(x_224, 4, x_219);
lean_ctor_set(x_224, 5, x_220);
lean_ctor_set(x_224, 6, x_223);
lean_ctor_set_uint8(x_224, sizeof(void*)*7, x_218);
x_225 = lean_st_ref_set(x_6, x_224, x_213);
x_226 = lean_ctor_get(x_225, 1);
lean_inc(x_226);
lean_dec(x_225);
x_227 = l_Lean_Compiler_LCNF_getType(x_142, x_8, x_9, x_10, x_11, x_226);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_230 = x_227;
} else {
 lean_dec_ref(x_227);
 x_230 = lean_box(0);
}
x_231 = lean_ctor_get(x_155, 2);
lean_inc(x_231);
x_232 = lean_ctor_get(x_155, 4);
lean_inc(x_232);
lean_dec(x_155);
x_233 = lean_alloc_ctor(0, 4, 3);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
lean_ctor_set(x_233, 2, x_228);
lean_ctor_set(x_233, 3, x_143);
lean_ctor_set_uint8(x_233, sizeof(void*)*4, x_208);
lean_ctor_set_uint8(x_233, sizeof(void*)*4 + 1, x_1);
lean_ctor_set_uint8(x_233, sizeof(void*)*4 + 2, x_1);
if (lean_is_scalar(x_156)) {
 x_234 = lean_alloc_ctor(1, 1, 0);
} else {
 x_234 = x_156;
}
lean_ctor_set(x_234, 0, x_233);
if (lean_is_scalar(x_230)) {
 x_235 = lean_alloc_ctor(0, 2, 0);
} else {
 x_235 = x_230;
}
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_229);
return x_235;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_143);
x_236 = lean_ctor_get(x_227, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_227, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_238 = x_227;
} else {
 lean_dec_ref(x_227);
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
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; 
x_245 = lean_ctor_get(x_144, 1);
lean_inc(x_245);
lean_dec(x_144);
x_246 = lean_ctor_get(x_145, 0);
lean_inc(x_246);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 x_247 = x_145;
} else {
 lean_dec_ref(x_145);
 x_247 = lean_box(0);
}
x_248 = lean_unsigned_to_nat(0u);
x_249 = lean_array_get_size(x_143);
x_250 = lean_nat_dec_lt(x_248, x_249);
lean_dec(x_249);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; 
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_143);
lean_dec(x_142);
x_251 = lean_box(0);
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_245);
return x_252;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; 
x_253 = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(x_246, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_245);
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_256 = x_253;
} else {
 lean_dec_ref(x_253);
 x_256 = lean_box(0);
}
if (x_3 == 0)
{
uint8_t x_290; 
x_290 = lean_unbox(x_254);
if (x_290 == 0)
{
lean_object* x_291; lean_object* x_292; 
lean_dec(x_254);
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_143);
lean_dec(x_142);
x_291 = lean_box(0);
if (lean_is_scalar(x_256)) {
 x_292 = lean_alloc_ctor(0, 2, 0);
} else {
 x_292 = x_256;
}
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_255);
return x_292;
}
else
{
uint8_t x_293; 
lean_dec(x_256);
x_293 = lean_unbox(x_254);
lean_dec(x_254);
x_257 = x_293;
goto block_289;
}
}
else
{
lean_dec(x_256);
lean_dec(x_254);
x_257 = x_3;
goto block_289;
}
block_289:
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_258 = l_Lean_Compiler_LCNF_Simp_incInlineLocal(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_255);
x_259 = lean_ctor_get(x_258, 1);
lean_inc(x_259);
lean_dec(x_258);
x_260 = lean_st_ref_take(x_6, x_259);
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_260, 1);
lean_inc(x_262);
lean_dec(x_260);
x_263 = lean_ctor_get(x_261, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_261, 1);
lean_inc(x_264);
x_265 = lean_ctor_get(x_261, 2);
lean_inc(x_265);
x_266 = lean_ctor_get(x_261, 3);
lean_inc(x_266);
x_267 = lean_ctor_get_uint8(x_261, sizeof(void*)*7);
x_268 = lean_ctor_get(x_261, 4);
lean_inc(x_268);
x_269 = lean_ctor_get(x_261, 5);
lean_inc(x_269);
x_270 = lean_ctor_get(x_261, 6);
lean_inc(x_270);
lean_dec(x_261);
x_271 = lean_unsigned_to_nat(1u);
x_272 = lean_nat_add(x_270, x_271);
lean_dec(x_270);
x_273 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_273, 0, x_263);
lean_ctor_set(x_273, 1, x_264);
lean_ctor_set(x_273, 2, x_265);
lean_ctor_set(x_273, 3, x_266);
lean_ctor_set(x_273, 4, x_268);
lean_ctor_set(x_273, 5, x_269);
lean_ctor_set(x_273, 6, x_272);
lean_ctor_set_uint8(x_273, sizeof(void*)*7, x_267);
x_274 = lean_st_ref_set(x_6, x_273, x_262);
x_275 = lean_ctor_get(x_274, 1);
lean_inc(x_275);
lean_dec(x_274);
x_276 = l_Lean_Compiler_LCNF_getType(x_142, x_8, x_9, x_10, x_11, x_275);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_279 = x_276;
} else {
 lean_dec_ref(x_276);
 x_279 = lean_box(0);
}
x_280 = lean_ctor_get(x_246, 2);
lean_inc(x_280);
x_281 = lean_ctor_get(x_246, 4);
lean_inc(x_281);
lean_dec(x_246);
x_282 = lean_alloc_ctor(0, 4, 3);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_281);
lean_ctor_set(x_282, 2, x_277);
lean_ctor_set(x_282, 3, x_143);
lean_ctor_set_uint8(x_282, sizeof(void*)*4, x_257);
lean_ctor_set_uint8(x_282, sizeof(void*)*4 + 1, x_1);
lean_ctor_set_uint8(x_282, sizeof(void*)*4 + 2, x_1);
if (lean_is_scalar(x_247)) {
 x_283 = lean_alloc_ctor(1, 1, 0);
} else {
 x_283 = x_247;
}
lean_ctor_set(x_283, 0, x_282);
if (lean_is_scalar(x_279)) {
 x_284 = lean_alloc_ctor(0, 2, 0);
} else {
 x_284 = x_279;
}
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_278);
return x_284;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_143);
x_285 = lean_ctor_get(x_276, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_276, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_287 = x_276;
} else {
 lean_dec_ref(x_276);
 x_287 = lean_box(0);
}
if (lean_is_scalar(x_287)) {
 x_288 = lean_alloc_ctor(1, 2, 0);
} else {
 x_288 = x_287;
}
lean_ctor_set(x_288, 0, x_285);
lean_ctor_set(x_288, 1, x_286);
return x_288;
}
}
}
}
}
}
else
{
lean_object* x_294; lean_object* x_295; 
lean_dec(x_2);
x_294 = lean_box(0);
x_295 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_12);
return x_295;
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_box(0);
x_14 = lean_box(x_3);
x_15 = lean_apply_11(x_1, x_2, x_14, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__1___boxed), 12, 1);
lean_closure_set(x_11, 0, x_10);
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
x_15 = lean_box(0);
switch (lean_obj_tag(x_12)) {
case 0:
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_14);
x_17 = lean_unbox(x_10);
x_18 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__2(x_11, x_1, x_17, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_16);
return x_18;
}
case 1:
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
switch (lean_obj_tag(x_19)) {
case 0:
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_mk_string_unchecked("inline", 6, 6);
x_22 = lean_string_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
lean_dec(x_21);
x_23 = l_Lean_Name_str___override(x_15, x_20);
x_24 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_13);
lean_ctor_set(x_24, 2, x_14);
x_25 = lean_unbox(x_10);
x_26 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__2(x_11, x_1, x_25, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_24);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_20);
x_27 = lean_array_get_size(x_14);
x_28 = lean_unsigned_to_nat(2u);
x_29 = lean_nat_dec_eq(x_27, x_28);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_30 = l_Lean_Name_str___override(x_15, x_21);
x_31 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_13);
lean_ctor_set(x_31, 2, x_14);
x_32 = lean_unbox(x_10);
x_33 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__2(x_11, x_1, x_32, x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_31);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_array_fget(x_14, x_34);
if (lean_obj_tag(x_35) == 1)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_1);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(x_36, x_6, x_9);
lean_dec(x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 0);
lean_dec(x_40);
x_41 = lean_box(0);
lean_ctor_set(x_37, 0, x_41);
return x_37;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_dec(x_37);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_37, 1);
lean_inc(x_45);
lean_dec(x_37);
x_46 = lean_ctor_get(x_38, 0);
lean_inc(x_46);
lean_dec(x_38);
x_47 = lean_ctor_get(x_46, 3);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_box(0);
x_49 = lean_unbox(x_10);
x_50 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__1(x_49, x_47, x_29, x_48, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_45);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_51 = l_Lean_Name_str___override(x_15, x_21);
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_array_fget(x_14, x_52);
lean_dec(x_14);
x_54 = lean_mk_empty_array_with_capacity(x_28);
x_55 = lean_array_push(x_54, x_53);
x_56 = lean_array_push(x_55, x_35);
x_57 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_57, 0, x_51);
lean_ctor_set(x_57, 1, x_13);
lean_ctor_set(x_57, 2, x_56);
x_58 = lean_unbox(x_10);
x_59 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__2(x_11, x_1, x_58, x_57, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_57);
return x_59;
}
}
}
}
case 1:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; 
x_60 = lean_ctor_get(x_12, 1);
lean_inc(x_60);
lean_dec(x_12);
x_61 = lean_ctor_get(x_19, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_19, 1);
lean_inc(x_62);
lean_dec(x_19);
x_63 = l_Lean_Name_str___override(x_61, x_62);
x_64 = l_Lean_Name_str___override(x_63, x_60);
x_65 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_13);
lean_ctor_set(x_65, 2, x_14);
x_66 = lean_unbox(x_10);
x_67 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__2(x_11, x_1, x_66, x_65, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_65);
return x_67;
}
default: 
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; 
x_68 = lean_ctor_get(x_12, 1);
lean_inc(x_68);
lean_dec(x_12);
x_69 = lean_ctor_get(x_19, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_19, 1);
lean_inc(x_70);
lean_dec(x_19);
x_71 = l_Lean_Name_num___override(x_69, x_70);
x_72 = l_Lean_Name_str___override(x_71, x_68);
x_73 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_13);
lean_ctor_set(x_73, 2, x_14);
x_74 = lean_unbox(x_10);
x_75 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__2(x_11, x_1, x_74, x_73, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_73);
return x_75;
}
}
}
default: 
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_12, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_12, 1);
lean_inc(x_77);
lean_dec(x_12);
x_78 = l_Lean_Name_num___override(x_76, x_77);
x_79 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_13);
lean_ctor_set(x_79, 2, x_14);
x_80 = lean_unbox(x_10);
x_81 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__2(x_11, x_1, x_80, x_79, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_79);
return x_81;
}
}
}
else
{
uint8_t x_82; lean_object* x_83; 
x_82 = lean_unbox(x_10);
lean_inc(x_1);
x_83 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__2(x_11, x_1, x_82, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_83;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__0(x_1, x_2, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__1(x_13, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__2(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_initFn____x40_Lean_Compiler_LCNF_Simp_InlineCandidate___hyg_1361_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_2 = lean_mk_string_unchecked("Compiler", 8, 8);
x_3 = lean_mk_string_unchecked("simp", 4, 4);
x_4 = lean_mk_string_unchecked("inline", 6, 6);
lean_inc(x_2);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_8);
x_9 = l_Lean_Name_str___override(x_7, x_8);
lean_inc(x_2);
x_10 = l_Lean_Name_str___override(x_9, x_2);
x_11 = lean_mk_string_unchecked("LCNF", 4, 4);
lean_inc(x_11);
x_12 = l_Lean_Name_str___override(x_10, x_11);
x_13 = lean_mk_string_unchecked("Simp", 4, 4);
lean_inc(x_13);
x_14 = l_Lean_Name_str___override(x_12, x_13);
x_15 = lean_mk_string_unchecked("initFn", 6, 6);
x_16 = l_Lean_Name_str___override(x_14, x_15);
x_17 = lean_mk_string_unchecked("_@", 2, 2);
x_18 = l_Lean_Name_str___override(x_16, x_17);
x_19 = l_Lean_Name_str___override(x_18, x_8);
x_20 = l_Lean_Name_str___override(x_19, x_2);
x_21 = l_Lean_Name_str___override(x_20, x_11);
x_22 = l_Lean_Name_str___override(x_21, x_13);
x_23 = lean_mk_string_unchecked("InlineCandidate", 15, 15);
x_24 = l_Lean_Name_str___override(x_22, x_23);
x_25 = lean_mk_string_unchecked("_hyg", 4, 4);
x_26 = l_Lean_Name_str___override(x_24, x_25);
x_27 = lean_unsigned_to_nat(1361u);
x_28 = l_Lean_Name_num___override(x_26, x_27);
x_29 = lean_unbox(x_6);
x_30 = l_Lean_registerTraceClass(x_5, x_29, x_28, x_1);
return x_30;
}
}
lean_object* initialize_Lean_Compiler_LCNF_Simp_SimpM(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_Compiler_LCNF_Simp_initFn____x40_Lean_Compiler_LCNF_Simp_InlineCandidate___hyg_1361_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
