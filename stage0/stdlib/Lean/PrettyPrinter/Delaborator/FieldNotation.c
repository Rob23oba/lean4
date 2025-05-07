// Lean compiler output
// Module: Lean.PrettyPrinter.Delaborator.FieldNotation
// Imports: Lean.Meta.InferType Lean.PrettyPrinter.Delaborator.Attributes Lean.PrettyPrinter.Delaborator.Options Lean.Structure
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_fieldNotationCandidate_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isParentProj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isParentProj(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_hasPPNoDotAttribute(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_typeMatchesBaseName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_fieldNotationCandidate_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isSubobjectField_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_fieldNotationCandidate_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_typeMatchesBaseName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_parentProj_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_fieldNotationCandidate_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_FVarId_getBinderInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_parentProj_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_parentProj_x3f(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_get_projection_info(lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_parentProj_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_st_ref_get(x_5, x_6);
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
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
lean_inc(x_21);
x_22 = lean_get_projection_info(x_21, x_1);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_16);
x_23 = lean_mk_string_unchecked("failed", 6, 6);
x_24 = l_Lean_stringToMessageData(x_23);
lean_dec(x_23);
x_25 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_24, x_2, x_3, x_4, x_5, x_19);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_37; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_box(0);
x_28 = l_Lean_Name_str___override(x_27, x_16);
x_37 = lean_ctor_get_uint8(x_26, sizeof(void*)*3);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_26, 0);
lean_inc(x_38);
lean_inc(x_21);
x_39 = l_Lean_Environment_find_x3f(x_21, x_38, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_21);
lean_dec(x_20);
x_7 = x_2;
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_19;
goto block_15;
}
else
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec(x_39);
if (lean_obj_tag(x_40) == 6)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
lean_inc(x_28);
x_43 = l_Lean_isSubobjectField_x3f(x_21, x_42, x_28);
if (lean_obj_tag(x_43) == 0)
{
x_29 = x_19;
x_30 = x_37;
goto block_36;
}
else
{
lean_object* x_44; uint8_t x_45; 
lean_dec(x_43);
x_44 = lean_box(1);
x_45 = lean_unbox(x_44);
x_29 = x_19;
x_30 = x_45;
goto block_36;
}
}
else
{
lean_dec(x_40);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_21);
lean_dec(x_20);
x_7 = x_2;
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_19;
goto block_15;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_21);
lean_dec(x_20);
x_46 = lean_mk_string_unchecked("failed", 6, 6);
x_47 = l_Lean_stringToMessageData(x_46);
lean_dec(x_46);
x_48 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_47, x_2, x_3, x_4, x_5, x_19);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
return x_48;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_48);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
block_36:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_dec(x_26);
x_32 = lean_box(x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_33);
if (lean_is_scalar(x_20)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_20;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_29);
return x_35;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_1);
x_53 = lean_mk_string_unchecked("failed", 6, 6);
x_54 = l_Lean_stringToMessageData(x_53);
lean_dec(x_53);
x_55 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_54, x_2, x_3, x_4, x_5, x_6);
return x_55;
}
block_15:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_mk_string_unchecked("failed", 6, 6);
x_13 = l_Lean_stringToMessageData(x_12);
lean_dec(x_12);
x_14 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_13, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_typeMatchesBaseName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
lean_inc(x_1);
x_8 = l_Lean_Expr_cleanupAnnotations(x_1);
x_9 = l_Lean_Expr_isAppOf(x_8, x_2);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lean_Meta_whnfR(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Lean_Expr_isAppOf(x_12, x_2);
lean_dec(x_12);
x_14 = lean_box(x_13);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = l_Lean_Expr_isAppOf(x_15, x_2);
lean_dec(x_15);
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
}
else
{
uint8_t x_20; 
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
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_24 = lean_box(x_9);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_7);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_typeMatchesBaseName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_typeMatchesBaseName(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_5, 1);
x_20 = lean_nat_dec_lt(x_7, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_12);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_6);
x_22 = lean_box(0);
x_23 = lean_box(0);
x_30 = lean_array_fget(x_2, x_7);
x_31 = l_Lean_Expr_fvarId_x21(x_30);
lean_dec(x_30);
lean_inc(x_8);
lean_inc(x_31);
x_32 = l_Lean_FVarId_getUserName(x_31, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_22);
lean_ctor_set(x_35, 1, x_23);
x_36 = l_Lean_Name_getPrefix(x_4);
x_118 = lean_mk_string_unchecked("motive", 6, 6);
x_119 = l_Lean_Name_mkStr1(x_118);
x_120 = lean_name_eq(x_33, x_119);
lean_dec(x_119);
lean_dec(x_33);
if (x_120 == 0)
{
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_64 = x_8;
x_65 = x_9;
x_66 = x_10;
x_67 = x_11;
x_68 = x_34;
goto block_117;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_7);
lean_dec(x_1);
x_121 = lean_mk_string_unchecked("failed", 6, 6);
x_122 = l_Lean_stringToMessageData(x_121);
lean_dec(x_121);
x_123 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_122, x_8, x_9, x_10, x_11, x_34);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_124 = !lean_is_exclusive(x_123);
if (x_124 == 0)
{
return x_123;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_123, 0);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_123);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
block_63:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = l_Lean_instInhabitedExpr;
x_43 = lean_array_get(x_42, x_3, x_7);
lean_inc(x_40);
lean_inc(x_37);
lean_inc(x_38);
lean_inc(x_39);
x_44 = lean_infer_type(x_43, x_39, x_38, x_37, x_40, x_41);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_45, x_38, x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_Lean_Expr_consumeMData(x_48);
lean_dec(x_48);
x_51 = l_Lean_Expr_isAppOf(x_50, x_36);
lean_dec(x_36);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_dec(x_7);
lean_dec(x_1);
x_52 = lean_mk_string_unchecked("failed", 6, 6);
x_53 = l_Lean_stringToMessageData(x_52);
lean_dec(x_52);
x_54 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_53, x_39, x_38, x_37, x_40, x_49);
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_38);
lean_dec(x_39);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
return x_54;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_54);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
else
{
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
x_24 = x_49;
goto block_29;
}
}
else
{
uint8_t x_59; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_7);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_44);
if (x_59 == 0)
{
return x_44;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_44, 0);
x_61 = lean_ctor_get(x_44, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_44);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
block_117:
{
lean_object* x_69; 
lean_inc(x_64);
lean_inc(x_31);
x_69 = l_Lean_FVarId_getType___redArg(x_31, x_64, x_66, x_67, x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
x_72 = l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_typeMatchesBaseName(x_70, x_36, x_64, x_65, x_66, x_67, x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
lean_dec(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_36);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
lean_inc(x_64);
x_76 = l_Lean_FVarId_getBinderInfo___redArg(x_31, x_64, x_66, x_67, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_unbox(x_77);
lean_dec(x_77);
x_80 = l_Lean_BinderInfo_isExplicit(x_79);
if (x_80 == 0)
{
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
x_13 = x_35;
x_14 = x_78;
goto block_18;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
lean_dec(x_35);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_81 = lean_mk_string_unchecked("failed", 6, 6);
x_82 = l_Lean_stringToMessageData(x_81);
lean_dec(x_81);
x_83 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_82, x_64, x_65, x_66, x_67, x_78);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
return x_83;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_83, 0);
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_83);
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
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_35);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_76);
if (x_88 == 0)
{
return x_76;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_76, 0);
x_90 = lean_ctor_get(x_76, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_76);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_35);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_92 = lean_ctor_get(x_72, 1);
lean_inc(x_92);
lean_dec(x_72);
lean_inc(x_64);
x_93 = l_Lean_FVarId_getBinderInfo___redArg(x_31, x_64, x_66, x_67, x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; uint8_t x_97; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_unbox(x_94);
lean_dec(x_94);
x_97 = l_Lean_BinderInfo_isExplicit(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
lean_dec(x_36);
lean_dec(x_7);
lean_dec(x_1);
x_98 = lean_mk_string_unchecked("failed", 6, 6);
x_99 = l_Lean_stringToMessageData(x_98);
lean_dec(x_98);
x_100 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_99, x_64, x_65, x_66, x_67, x_95);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
return x_100;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_100, 0);
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_100);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
else
{
x_37 = x_66;
x_38 = x_65;
x_39 = x_64;
x_40 = x_67;
x_41 = x_95;
goto block_63;
}
}
else
{
uint8_t x_105; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_36);
lean_dec(x_7);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_93);
if (x_105 == 0)
{
return x_93;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_93, 0);
x_107 = lean_ctor_get(x_93, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_93);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_72);
if (x_109 == 0)
{
return x_72;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_72, 0);
x_111 = lean_ctor_get(x_72, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_72);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_113 = !lean_is_exclusive(x_69);
if (x_113 == 0)
{
return x_69;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_69, 0);
x_115 = lean_ctor_get(x_69, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_69);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_31);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_32);
if (x_128 == 0)
{
return x_32;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_32, 0);
x_130 = lean_ctor_get(x_32, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_32);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
block_29:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_7);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
return x_28;
}
}
block_18:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_5, 2);
x_16 = lean_nat_add(x_7, x_15);
lean_dec(x_7);
x_6 = x_13;
x_7 = x_16;
x_12 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_5, 1);
x_20 = lean_nat_dec_lt(x_7, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_12);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_6);
x_22 = lean_box(0);
x_23 = lean_box(0);
x_30 = lean_array_fget(x_2, x_7);
x_31 = l_Lean_Expr_fvarId_x21(x_30);
lean_dec(x_30);
lean_inc(x_8);
lean_inc(x_31);
x_32 = l_Lean_FVarId_getUserName(x_31, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_22);
lean_ctor_set(x_35, 1, x_23);
x_36 = l_Lean_Name_getPrefix(x_4);
x_118 = lean_mk_string_unchecked("motive", 6, 6);
x_119 = l_Lean_Name_mkStr1(x_118);
x_120 = lean_name_eq(x_33, x_119);
lean_dec(x_119);
lean_dec(x_33);
if (x_120 == 0)
{
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_64 = x_8;
x_65 = x_9;
x_66 = x_10;
x_67 = x_11;
x_68 = x_34;
goto block_117;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_7);
lean_dec(x_1);
x_121 = lean_mk_string_unchecked("failed", 6, 6);
x_122 = l_Lean_stringToMessageData(x_121);
lean_dec(x_121);
x_123 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_122, x_8, x_9, x_10, x_11, x_34);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_124 = !lean_is_exclusive(x_123);
if (x_124 == 0)
{
return x_123;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_123, 0);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_123);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
block_63:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = l_Lean_instInhabitedExpr;
x_43 = lean_array_get(x_42, x_3, x_7);
lean_inc(x_38);
lean_inc(x_40);
lean_inc(x_37);
lean_inc(x_39);
x_44 = lean_infer_type(x_43, x_39, x_37, x_40, x_38, x_41);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_45, x_37, x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_Lean_Expr_consumeMData(x_48);
lean_dec(x_48);
x_51 = l_Lean_Expr_isAppOf(x_50, x_36);
lean_dec(x_36);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_dec(x_7);
lean_dec(x_1);
x_52 = lean_mk_string_unchecked("failed", 6, 6);
x_53 = l_Lean_stringToMessageData(x_52);
lean_dec(x_52);
x_54 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_53, x_39, x_37, x_40, x_38, x_49);
lean_dec(x_38);
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_39);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
return x_54;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_54);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
else
{
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
x_24 = x_49;
goto block_29;
}
}
else
{
uint8_t x_59; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_7);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_44);
if (x_59 == 0)
{
return x_44;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_44, 0);
x_61 = lean_ctor_get(x_44, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_44);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
block_117:
{
lean_object* x_69; 
lean_inc(x_64);
lean_inc(x_31);
x_69 = l_Lean_FVarId_getType___redArg(x_31, x_64, x_66, x_67, x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
x_72 = l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_typeMatchesBaseName(x_70, x_36, x_64, x_65, x_66, x_67, x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
lean_dec(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_36);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
lean_inc(x_64);
x_76 = l_Lean_FVarId_getBinderInfo___redArg(x_31, x_64, x_66, x_67, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_unbox(x_77);
lean_dec(x_77);
x_80 = l_Lean_BinderInfo_isExplicit(x_79);
if (x_80 == 0)
{
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
x_13 = x_35;
x_14 = x_78;
goto block_18;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
lean_dec(x_35);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_81 = lean_mk_string_unchecked("failed", 6, 6);
x_82 = l_Lean_stringToMessageData(x_81);
lean_dec(x_81);
x_83 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_82, x_64, x_65, x_66, x_67, x_78);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
return x_83;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_83, 0);
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_83);
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
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_35);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_76);
if (x_88 == 0)
{
return x_76;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_76, 0);
x_90 = lean_ctor_get(x_76, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_76);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_35);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_92 = lean_ctor_get(x_72, 1);
lean_inc(x_92);
lean_dec(x_72);
lean_inc(x_64);
x_93 = l_Lean_FVarId_getBinderInfo___redArg(x_31, x_64, x_66, x_67, x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; uint8_t x_97; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_unbox(x_94);
lean_dec(x_94);
x_97 = l_Lean_BinderInfo_isExplicit(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
lean_dec(x_36);
lean_dec(x_7);
lean_dec(x_1);
x_98 = lean_mk_string_unchecked("failed", 6, 6);
x_99 = l_Lean_stringToMessageData(x_98);
lean_dec(x_98);
x_100 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_99, x_64, x_65, x_66, x_67, x_95);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
return x_100;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_100, 0);
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_100);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
else
{
x_37 = x_65;
x_38 = x_67;
x_39 = x_64;
x_40 = x_66;
x_41 = x_95;
goto block_63;
}
}
else
{
uint8_t x_105; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_36);
lean_dec(x_7);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_93);
if (x_105 == 0)
{
return x_93;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_93, 0);
x_107 = lean_ctor_get(x_93, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_93);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_72);
if (x_109 == 0)
{
return x_72;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_72, 0);
x_111 = lean_ctor_get(x_72, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_72);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_113 = !lean_is_exclusive(x_69);
if (x_113 == 0)
{
return x_69;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_69, 0);
x_115 = lean_ctor_get(x_69, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_69);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_31);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_32);
if (x_128 == 0)
{
return x_32;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_32, 0);
x_130 = lean_ctor_get(x_32, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_32);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
block_29:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_7);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
return x_28;
}
}
block_18:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_5, 2);
x_16 = lean_nat_add(x_7, x_15);
lean_dec(x_7);
x_17 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_13, x_16, x_8, x_9, x_10, x_11, x_14);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_x27_loop___at_____private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get_size(x_4);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_box(0);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = l_Std_Range_forIn_x27_loop___at_____private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__0___redArg(x_1, x_4, x_2, x_3, x_14, x_17, x_11, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_mk_string_unchecked("failed", 6, 6);
x_23 = l_Lean_stringToMessageData(x_22);
lean_dec(x_22);
x_24 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_23, x_6, x_7, x_8, x_9, x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_18, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_20, 0);
lean_inc(x_27);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_27);
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_ctor_get(x_20, 0);
lean_inc(x_29);
lean_dec(x_20);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_31 = !lean_is_exclusive(x_18);
if (x_31 == 0)
{
return x_18;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_18);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_box(0);
x_10 = l_Lean_Name_str___override(x_9, x_8);
lean_inc(x_1);
lean_inc(x_2);
x_11 = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo___lam__0___boxed), 10, 3);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_1);
x_12 = l_Lean_Name_getPrefix(x_1);
x_13 = l_Lean_Name_isAnonymous(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_mk_string_unchecked("Function", 8, 8);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = lean_name_eq(x_12, x_15);
lean_dec(x_15);
lean_dec(x_12);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_ConstantInfo_type(x_18);
lean_dec(x_18);
x_21 = lean_array_get_size(x_2);
lean_dec(x_2);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6(lean_box(0), x_20, x_22, x_11, x_16, x_3, x_4, x_5, x_6, x_19);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_17, 0);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_17);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_mk_string_unchecked("failed", 6, 6);
x_29 = l_Lean_stringToMessageData(x_28);
lean_dec(x_28);
x_30 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_29, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_30);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_35 = lean_mk_string_unchecked("failed", 6, 6);
x_36 = l_Lean_stringToMessageData(x_35);
lean_dec(x_35);
x_37 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_36, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
return x_37;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_37);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_2);
lean_dec(x_1);
x_42 = lean_mk_string_unchecked("failed", 6, 6);
x_43 = l_Lean_stringToMessageData(x_42);
lean_dec(x_42);
x_44 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_43, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_44;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at_____private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_x27_loop___at_____private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_fieldNotationCandidate_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_fieldNotationCandidate_x3f(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_18; lean_object* x_19; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_st_ref_get(x_7, x_8);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_26 = x_23;
} else {
 lean_dec_ref(x_23);
 x_26 = lean_box(0);
}
x_27 = l_Lean_Expr_consumeMData(x_1);
switch (lean_obj_tag(x_27)) {
case 0:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_Expr_bvar___override(x_28);
x_30 = l_Lean_PrettyPrinter_Delaborator_fieldNotationCandidate_x3f___lam__0(x_29, x_4, x_5, x_6, x_7, x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_29);
return x_30;
}
case 1:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_ctor_get(x_27, 0);
lean_inc(x_31);
lean_dec(x_27);
x_32 = l_Lean_Expr_fvar___override(x_31);
x_33 = l_Lean_PrettyPrinter_Delaborator_fieldNotationCandidate_x3f___lam__0(x_32, x_4, x_5, x_6, x_7, x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_32);
return x_33;
}
case 2:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_ctor_get(x_27, 0);
lean_inc(x_34);
lean_dec(x_27);
x_35 = l_Lean_Expr_mvar___override(x_34);
x_36 = l_Lean_PrettyPrinter_Delaborator_fieldNotationCandidate_x3f___lam__0(x_35, x_4, x_5, x_6, x_7, x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_35);
return x_36;
}
case 3:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_2);
lean_dec(x_1);
x_37 = lean_ctor_get(x_27, 0);
lean_inc(x_37);
lean_dec(x_27);
x_38 = l_Lean_Expr_sort___override(x_37);
x_39 = l_Lean_PrettyPrinter_Delaborator_fieldNotationCandidate_x3f___lam__0(x_38, x_4, x_5, x_6, x_7, x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_38);
return x_39;
}
case 4:
{
lean_object* x_40; lean_object* x_41; lean_object* x_53; uint8_t x_54; 
x_40 = lean_ctor_get(x_27, 0);
lean_inc(x_40);
lean_dec(x_27);
x_53 = l_Lean_Name_getPrefix(x_40);
x_54 = l_Lean_Name_isAnonymous(x_53);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_75; lean_object* x_76; 
x_55 = lean_ctor_get(x_24, 0);
lean_inc(x_55);
lean_dec(x_24);
x_56 = l_Lean_hasPPNoDotAttribute(x_55, x_40);
if (x_56 == 0)
{
lean_object* x_80; 
lean_inc(x_40);
x_80 = l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo(x_40, x_4, x_5, x_6, x_7, x_25);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
x_83 = !lean_is_exclusive(x_80);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_84 = lean_ctor_get(x_80, 1);
x_85 = lean_ctor_get(x_80, 0);
lean_dec(x_85);
x_86 = lean_ctor_get(x_81, 0);
lean_inc(x_86);
lean_dec(x_81);
x_87 = !lean_is_exclusive(x_82);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_88 = lean_ctor_get(x_82, 0);
x_89 = lean_ctor_get(x_82, 1);
lean_dec(x_89);
x_90 = lean_unsigned_to_nat(1u);
x_91 = lean_nat_add(x_88, x_90);
x_92 = lean_array_get_size(x_2);
x_93 = lean_nat_dec_le(x_91, x_92);
lean_dec(x_92);
lean_dec(x_91);
if (x_93 == 0)
{
lean_object* x_94; 
lean_free_object(x_82);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_53);
lean_dec(x_40);
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_94 = lean_box(0);
lean_ctor_set(x_80, 0, x_94);
return x_80;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_free_object(x_80);
x_95 = l_Lean_instInhabitedExpr;
x_96 = lean_array_get(x_95, x_2, x_88);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_97 = lean_infer_type(x_96, x_4, x_5, x_6, x_7, x_84);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_100 = lean_whnf(x_98, x_4, x_5, x_6, x_7, x_99);
if (lean_obj_tag(x_100) == 0)
{
uint8_t x_101; 
lean_dec(x_40);
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
lean_object* x_102; uint8_t x_103; 
x_102 = lean_ctor_get(x_100, 0);
x_103 = l_Lean_Expr_isAppOf(x_102, x_53);
lean_dec(x_53);
lean_dec(x_102);
if (x_103 == 0)
{
lean_object* x_104; 
lean_free_object(x_82);
lean_dec(x_88);
lean_dec(x_86);
x_104 = lean_box(0);
lean_ctor_set(x_100, 0, x_104);
return x_100;
}
else
{
lean_object* x_105; 
lean_ctor_set(x_82, 1, x_88);
lean_ctor_set(x_82, 0, x_86);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_82);
lean_ctor_set(x_100, 0, x_105);
return x_100;
}
}
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_106 = lean_ctor_get(x_100, 0);
x_107 = lean_ctor_get(x_100, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_100);
x_108 = l_Lean_Expr_isAppOf(x_106, x_53);
lean_dec(x_53);
lean_dec(x_106);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
lean_free_object(x_82);
lean_dec(x_88);
lean_dec(x_86);
x_109 = lean_box(0);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_107);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; 
lean_ctor_set(x_82, 1, x_88);
lean_ctor_set(x_82, 0, x_86);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_82);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_107);
return x_112;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; 
lean_free_object(x_82);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_53);
x_113 = lean_ctor_get(x_100, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_100, 1);
lean_inc(x_114);
lean_dec(x_100);
x_75 = x_113;
x_76 = x_114;
goto block_79;
}
}
else
{
lean_object* x_115; lean_object* x_116; 
lean_free_object(x_82);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_53);
x_115 = lean_ctor_get(x_97, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_97, 1);
lean_inc(x_116);
lean_dec(x_97);
x_75 = x_115;
x_76 = x_116;
goto block_79;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_117 = lean_ctor_get(x_82, 0);
lean_inc(x_117);
lean_dec(x_82);
x_118 = lean_unsigned_to_nat(1u);
x_119 = lean_nat_add(x_117, x_118);
x_120 = lean_array_get_size(x_2);
x_121 = lean_nat_dec_le(x_119, x_120);
lean_dec(x_120);
lean_dec(x_119);
if (x_121 == 0)
{
lean_object* x_122; 
lean_dec(x_117);
lean_dec(x_86);
lean_dec(x_53);
lean_dec(x_40);
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_122 = lean_box(0);
lean_ctor_set(x_80, 0, x_122);
return x_80;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_free_object(x_80);
x_123 = l_Lean_instInhabitedExpr;
x_124 = lean_array_get(x_123, x_2, x_117);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_125 = lean_infer_type(x_124, x_4, x_5, x_6, x_7, x_84);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_128 = lean_whnf(x_126, x_4, x_5, x_6, x_7, x_127);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
lean_dec(x_40);
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_131 = x_128;
} else {
 lean_dec_ref(x_128);
 x_131 = lean_box(0);
}
x_132 = l_Lean_Expr_isAppOf(x_129, x_53);
lean_dec(x_53);
lean_dec(x_129);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; 
lean_dec(x_117);
lean_dec(x_86);
x_133 = lean_box(0);
if (lean_is_scalar(x_131)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_131;
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_130);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_86);
lean_ctor_set(x_135, 1, x_117);
x_136 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_136, 0, x_135);
if (lean_is_scalar(x_131)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_131;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_130);
return x_137;
}
}
else
{
lean_object* x_138; lean_object* x_139; 
lean_dec(x_117);
lean_dec(x_86);
lean_dec(x_53);
x_138 = lean_ctor_get(x_128, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_128, 1);
lean_inc(x_139);
lean_dec(x_128);
x_75 = x_138;
x_76 = x_139;
goto block_79;
}
}
else
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_117);
lean_dec(x_86);
lean_dec(x_53);
x_140 = lean_ctor_get(x_125, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_125, 1);
lean_inc(x_141);
lean_dec(x_125);
x_75 = x_140;
x_76 = x_141;
goto block_79;
}
}
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_142 = lean_ctor_get(x_80, 1);
lean_inc(x_142);
lean_dec(x_80);
x_143 = lean_ctor_get(x_81, 0);
lean_inc(x_143);
lean_dec(x_81);
x_144 = lean_ctor_get(x_82, 0);
lean_inc(x_144);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_145 = x_82;
} else {
 lean_dec_ref(x_82);
 x_145 = lean_box(0);
}
x_146 = lean_unsigned_to_nat(1u);
x_147 = lean_nat_add(x_144, x_146);
x_148 = lean_array_get_size(x_2);
x_149 = lean_nat_dec_le(x_147, x_148);
lean_dec(x_148);
lean_dec(x_147);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_53);
lean_dec(x_40);
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_150 = lean_box(0);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_142);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = l_Lean_instInhabitedExpr;
x_153 = lean_array_get(x_152, x_2, x_144);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_154 = lean_infer_type(x_153, x_4, x_5, x_6, x_7, x_142);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_157 = lean_whnf(x_155, x_4, x_5, x_6, x_7, x_156);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
lean_dec(x_40);
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_160 = x_157;
} else {
 lean_dec_ref(x_157);
 x_160 = lean_box(0);
}
x_161 = l_Lean_Expr_isAppOf(x_158, x_53);
lean_dec(x_53);
lean_dec(x_158);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; 
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_143);
x_162 = lean_box(0);
if (lean_is_scalar(x_160)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_160;
}
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_159);
return x_163;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
if (lean_is_scalar(x_145)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_145;
}
lean_ctor_set(x_164, 0, x_143);
lean_ctor_set(x_164, 1, x_144);
x_165 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_165, 0, x_164);
if (lean_is_scalar(x_160)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_160;
}
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_159);
return x_166;
}
}
else
{
lean_object* x_167; lean_object* x_168; 
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_53);
x_167 = lean_ctor_get(x_157, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_157, 1);
lean_inc(x_168);
lean_dec(x_157);
x_75 = x_167;
x_76 = x_168;
goto block_79;
}
}
else
{
lean_object* x_169; lean_object* x_170; 
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_53);
x_169 = lean_ctor_get(x_154, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_154, 1);
lean_inc(x_170);
lean_dec(x_154);
x_75 = x_169;
x_76 = x_170;
goto block_79;
}
}
}
}
else
{
lean_object* x_171; lean_object* x_172; 
lean_dec(x_53);
x_171 = lean_ctor_get(x_80, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_80, 1);
lean_inc(x_172);
lean_dec(x_80);
x_75 = x_171;
x_76 = x_172;
goto block_79;
}
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_53);
lean_dec(x_40);
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_173 = lean_box(0);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_25);
return x_174;
}
block_74:
{
if (x_59 == 0)
{
lean_dec(x_57);
lean_dec(x_26);
if (x_3 == 0)
{
lean_dec(x_40);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_9 = x_58;
goto block_12;
}
else
{
lean_object* x_60; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_60 = l_Lean_Meta_isProof(x_1, x_4, x_5, x_6, x_7, x_58);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_unbox(x_61);
lean_dec(x_61);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_41 = x_63;
goto block_52;
}
else
{
if (x_56 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_40);
lean_dec(x_2);
x_64 = lean_ctor_get(x_60, 1);
lean_inc(x_64);
lean_dec(x_60);
x_65 = lean_mk_string_unchecked("failed", 6, 6);
x_66 = l_Lean_stringToMessageData(x_65);
lean_dec(x_65);
x_67 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_66, x_4, x_5, x_6, x_7, x_64);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_18 = x_68;
x_19 = x_69;
goto block_22;
}
else
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_60, 1);
lean_inc(x_70);
lean_dec(x_60);
x_41 = x_70;
goto block_52;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_40);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_71 = lean_ctor_get(x_60, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_60, 1);
lean_inc(x_72);
lean_dec(x_60);
x_18 = x_71;
x_19 = x_72;
goto block_22;
}
}
}
else
{
lean_object* x_73; 
lean_dec(x_40);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_26)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_26;
 lean_ctor_set_tag(x_73, 1);
}
lean_ctor_set(x_73, 0, x_57);
lean_ctor_set(x_73, 1, x_58);
return x_73;
}
}
block_79:
{
uint8_t x_77; 
x_77 = l_Lean_Exception_isInterrupt(x_75);
if (x_77 == 0)
{
uint8_t x_78; 
x_78 = l_Lean_Exception_isRuntime(x_75);
x_57 = x_75;
x_58 = x_76;
x_59 = x_78;
goto block_74;
}
else
{
x_57 = x_75;
x_58 = x_76;
x_59 = x_77;
goto block_74;
}
}
}
else
{
lean_object* x_175; lean_object* x_176; 
lean_dec(x_53);
lean_dec(x_40);
lean_dec(x_24);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_175 = lean_box(0);
if (lean_is_scalar(x_26)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_26;
}
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_25);
return x_176;
}
block_52:
{
lean_object* x_42; 
x_42 = l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo(x_40, x_2, x_4, x_5, x_6, x_7, x_41);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_42, 0, x_45);
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_42, 0);
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_42);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_46);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_42, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_42, 1);
lean_inc(x_51);
lean_dec(x_42);
x_18 = x_50;
x_19 = x_51;
goto block_22;
}
}
}
case 5:
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_2);
lean_dec(x_1);
x_177 = lean_ctor_get(x_27, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_27, 1);
lean_inc(x_178);
lean_dec(x_27);
x_179 = l_Lean_Expr_app___override(x_177, x_178);
x_180 = l_Lean_PrettyPrinter_Delaborator_fieldNotationCandidate_x3f___lam__0(x_179, x_4, x_5, x_6, x_7, x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_179);
return x_180;
}
case 6:
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_2);
lean_dec(x_1);
x_181 = lean_ctor_get(x_27, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_27, 1);
lean_inc(x_182);
x_183 = lean_ctor_get(x_27, 2);
lean_inc(x_183);
x_184 = lean_ctor_get_uint8(x_27, sizeof(void*)*3 + 8);
lean_dec(x_27);
x_185 = l_Lean_Expr_lam___override(x_181, x_182, x_183, x_184);
x_186 = l_Lean_PrettyPrinter_Delaborator_fieldNotationCandidate_x3f___lam__0(x_185, x_4, x_5, x_6, x_7, x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_185);
return x_186;
}
case 7:
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_2);
lean_dec(x_1);
x_187 = lean_ctor_get(x_27, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_27, 1);
lean_inc(x_188);
x_189 = lean_ctor_get(x_27, 2);
lean_inc(x_189);
x_190 = lean_ctor_get_uint8(x_27, sizeof(void*)*3 + 8);
lean_dec(x_27);
x_191 = l_Lean_Expr_forallE___override(x_187, x_188, x_189, x_190);
x_192 = l_Lean_PrettyPrinter_Delaborator_fieldNotationCandidate_x3f___lam__0(x_191, x_4, x_5, x_6, x_7, x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_191);
return x_192;
}
case 8:
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_2);
lean_dec(x_1);
x_193 = lean_ctor_get(x_27, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_27, 1);
lean_inc(x_194);
x_195 = lean_ctor_get(x_27, 2);
lean_inc(x_195);
x_196 = lean_ctor_get(x_27, 3);
lean_inc(x_196);
x_197 = lean_ctor_get_uint8(x_27, sizeof(void*)*4 + 8);
lean_dec(x_27);
x_198 = l_Lean_Expr_letE___override(x_193, x_194, x_195, x_196, x_197);
x_199 = l_Lean_PrettyPrinter_Delaborator_fieldNotationCandidate_x3f___lam__0(x_198, x_4, x_5, x_6, x_7, x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_198);
return x_199;
}
case 9:
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_2);
lean_dec(x_1);
x_200 = lean_ctor_get(x_27, 0);
lean_inc(x_200);
lean_dec(x_27);
x_201 = l_Lean_Expr_lit___override(x_200);
x_202 = l_Lean_PrettyPrinter_Delaborator_fieldNotationCandidate_x3f___lam__0(x_201, x_4, x_5, x_6, x_7, x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_201);
return x_202;
}
case 10:
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_2);
lean_dec(x_1);
x_203 = lean_ctor_get(x_27, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_27, 1);
lean_inc(x_204);
lean_dec(x_27);
x_205 = l_Lean_Expr_mdata___override(x_203, x_204);
x_206 = l_Lean_PrettyPrinter_Delaborator_fieldNotationCandidate_x3f___lam__0(x_205, x_4, x_5, x_6, x_7, x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_205);
return x_206;
}
default: 
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_2);
lean_dec(x_1);
x_207 = lean_ctor_get(x_27, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_27, 1);
lean_inc(x_208);
x_209 = lean_ctor_get(x_27, 2);
lean_inc(x_209);
lean_dec(x_27);
x_210 = l_Lean_Expr_proj___override(x_207, x_208, x_209);
x_211 = l_Lean_PrettyPrinter_Delaborator_fieldNotationCandidate_x3f___lam__0(x_210, x_4, x_5, x_6, x_7, x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_210);
return x_211;
}
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
block_17:
{
if (x_15 == 0)
{
lean_dec(x_13);
x_9 = x_14;
goto block_12;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
block_22:
{
uint8_t x_20; 
x_20 = l_Lean_Exception_isInterrupt(x_18);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = l_Lean_Exception_isRuntime(x_18);
x_13 = x_18;
x_14 = x_19;
x_15 = x_21;
goto block_17;
}
else
{
x_13 = x_18;
x_14 = x_19;
x_15 = x_20;
goto block_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_fieldNotationCandidate_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Delaborator_fieldNotationCandidate_x3f___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_fieldNotationCandidate_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_PrettyPrinter_Delaborator_fieldNotationCandidate_x3f(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_parentProj_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_mk_string_unchecked("failed", 6, 6);
x_8 = l_Lean_stringToMessageData(x_7);
lean_dec(x_7);
x_9 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_8, x_2, x_3, x_4, x_5, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_parentProj_x3f(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_15; lean_object* x_16; lean_object* x_20; uint8_t x_24; 
x_24 = l_Lean_Expr_isApp(x_2);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_7);
return x_26;
}
else
{
lean_object* x_27; 
x_27 = l_Lean_Expr_getAppFn(x_2);
switch (lean_obj_tag(x_27)) {
case 0:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_Expr_bvar___override(x_28);
x_30 = l_Lean_PrettyPrinter_Delaborator_parentProj_x3f___lam__0(x_29, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_29);
x_20 = x_30;
goto block_23;
}
case 1:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 0);
lean_inc(x_31);
lean_dec(x_27);
x_32 = l_Lean_Expr_fvar___override(x_31);
x_33 = l_Lean_PrettyPrinter_Delaborator_parentProj_x3f___lam__0(x_32, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_32);
x_20 = x_33;
goto block_23;
}
case 2:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_27, 0);
lean_inc(x_34);
lean_dec(x_27);
x_35 = l_Lean_Expr_mvar___override(x_34);
x_36 = l_Lean_PrettyPrinter_Delaborator_parentProj_x3f___lam__0(x_35, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_35);
x_20 = x_36;
goto block_23;
}
case 3:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_27, 0);
lean_inc(x_37);
lean_dec(x_27);
x_38 = l_Lean_Expr_sort___override(x_37);
x_39 = l_Lean_PrettyPrinter_Delaborator_parentProj_x3f___lam__0(x_38, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_38);
x_20 = x_39;
goto block_23;
}
case 4:
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_27, 0);
lean_inc(x_40);
lean_dec(x_27);
x_41 = l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo(x_40, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_60; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_42, 0);
lean_inc(x_49);
lean_dec(x_42);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_52 = x_48;
} else {
 lean_dec_ref(x_48);
 x_52 = lean_box(0);
}
x_60 = lean_unbox(x_51);
lean_dec(x_51);
if (x_60 == 0)
{
lean_dec(x_52);
lean_dec(x_50);
lean_dec(x_49);
goto block_47;
}
else
{
if (x_1 == 0)
{
goto block_59;
}
else
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_nat_dec_eq(x_50, x_61);
if (x_62 == 0)
{
lean_dec(x_52);
lean_dec(x_50);
lean_dec(x_49);
goto block_47;
}
else
{
goto block_59;
}
}
}
block_47:
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_box(0);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
block_59:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = l_Lean_Expr_getAppNumArgs(x_2);
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_50, x_54);
lean_dec(x_50);
x_56 = lean_nat_dec_eq(x_53, x_55);
lean_dec(x_55);
lean_dec(x_53);
if (x_56 == 0)
{
lean_dec(x_52);
lean_dec(x_49);
goto block_47;
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_44);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_49);
if (lean_is_scalar(x_52)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_52;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_43);
return x_58;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_41, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_41, 1);
lean_inc(x_64);
lean_dec(x_41);
x_15 = x_63;
x_16 = x_64;
goto block_19;
}
}
case 5:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_27, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_27, 1);
lean_inc(x_66);
lean_dec(x_27);
x_67 = l_Lean_Expr_app___override(x_65, x_66);
x_68 = l_Lean_PrettyPrinter_Delaborator_parentProj_x3f___lam__0(x_67, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_67);
x_20 = x_68;
goto block_23;
}
case 6:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; 
x_69 = lean_ctor_get(x_27, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_27, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_27, 2);
lean_inc(x_71);
x_72 = lean_ctor_get_uint8(x_27, sizeof(void*)*3 + 8);
lean_dec(x_27);
x_73 = l_Lean_Expr_lam___override(x_69, x_70, x_71, x_72);
x_74 = l_Lean_PrettyPrinter_Delaborator_parentProj_x3f___lam__0(x_73, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_73);
x_20 = x_74;
goto block_23;
}
case 7:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_27, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_27, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_27, 2);
lean_inc(x_77);
x_78 = lean_ctor_get_uint8(x_27, sizeof(void*)*3 + 8);
lean_dec(x_27);
x_79 = l_Lean_Expr_forallE___override(x_75, x_76, x_77, x_78);
x_80 = l_Lean_PrettyPrinter_Delaborator_parentProj_x3f___lam__0(x_79, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_79);
x_20 = x_80;
goto block_23;
}
case 8:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; 
x_81 = lean_ctor_get(x_27, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_27, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_27, 2);
lean_inc(x_83);
x_84 = lean_ctor_get(x_27, 3);
lean_inc(x_84);
x_85 = lean_ctor_get_uint8(x_27, sizeof(void*)*4 + 8);
lean_dec(x_27);
x_86 = l_Lean_Expr_letE___override(x_81, x_82, x_83, x_84, x_85);
x_87 = l_Lean_PrettyPrinter_Delaborator_parentProj_x3f___lam__0(x_86, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_86);
x_20 = x_87;
goto block_23;
}
case 9:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_27, 0);
lean_inc(x_88);
lean_dec(x_27);
x_89 = l_Lean_Expr_lit___override(x_88);
x_90 = l_Lean_PrettyPrinter_Delaborator_parentProj_x3f___lam__0(x_89, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_89);
x_20 = x_90;
goto block_23;
}
case 10:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_27, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_27, 1);
lean_inc(x_92);
lean_dec(x_27);
x_93 = l_Lean_Expr_mdata___override(x_91, x_92);
x_94 = l_Lean_PrettyPrinter_Delaborator_parentProj_x3f___lam__0(x_93, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_93);
x_20 = x_94;
goto block_23;
}
default: 
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_95 = lean_ctor_get(x_27, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_27, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_27, 2);
lean_inc(x_97);
lean_dec(x_27);
x_98 = l_Lean_Expr_proj___override(x_95, x_96, x_97);
x_99 = l_Lean_PrettyPrinter_Delaborator_parentProj_x3f___lam__0(x_98, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_98);
x_20 = x_99;
goto block_23;
}
}
}
block_14:
{
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
}
block_19:
{
uint8_t x_17; 
x_17 = l_Lean_Exception_isInterrupt(x_15);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = l_Lean_Exception_isRuntime(x_15);
x_8 = x_16;
x_9 = x_15;
x_10 = x_18;
goto block_14;
}
else
{
x_8 = x_16;
x_9 = x_15;
x_10 = x_17;
goto block_14;
}
}
block_23:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_15 = x_21;
x_16 = x_22;
goto block_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_parentProj_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Delaborator_parentProj_x3f___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_parentProj_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_PrettyPrinter_Delaborator_parentProj_x3f(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isParentProj(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Delaborator_parentProj_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_9);
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_8, 0);
lean_dec(x_17);
x_18 = lean_box(1);
lean_ctor_set(x_8, 0, x_18);
return x_8;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_dec(x_8);
x_20 = lean_box(1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_8);
if (x_22 == 0)
{
return x_8;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_8, 0);
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_8);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isParentProj___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_PrettyPrinter_Delaborator_isParentProj(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* initialize_Lean_Meta_InferType(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_PrettyPrinter_Delaborator_Attributes(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_PrettyPrinter_Delaborator_Options(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Structure(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_PrettyPrinter_Delaborator_FieldNotation(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_InferType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Delaborator_Attributes(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Delaborator_Options(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Structure(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
