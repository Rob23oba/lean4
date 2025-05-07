// Lean compiler output
// Module: Lean.Compiler.LCNF.ToDecl
// Imports: Lean.Meta.Transform Lean.Meta.Match.MatcherInfo Lean.Compiler.ExternAttr Lean.Compiler.InitAttr Lean.Compiler.ImplementedByAttr Lean.Compiler.LCNF.ToLCNF
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstAltPos(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lam__2(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_hasMacroInlineAttribute(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*, uint8_t);
uint8_t l_Lean_hasInitAttr(lean_object*, lean_object*);
lean_object* lean_get_extern_attr_data(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Compiler_LCNF_toLCNFType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseFunDecl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Compiler_LCNF_toDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
uint8_t lean_is_marked_borrowed(lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Compiler_LCNF_toDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___redArg(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_getType_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_is_unsafe_rec_name(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkParam(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___at___Lean_Core_betaReduce_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_unsafe_rec_name(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform___at___Lean_Meta_zetaReduce_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_reduceMatcher_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_getInlineAttribute_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_isPartial(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_getConstInfo___at_____private_Lean_Compiler_LCNF_Util_0__Lean_Compiler_LCNF_getCasesOnInductiveVal_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Expr_getAppFn(x_2);
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Expr_bvar___override(x_7);
x_9 = lean_apply_4(x_1, x_8, x_3, x_4, x_5);
return x_9;
}
case 1:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lean_Expr_fvar___override(x_10);
x_12 = lean_apply_4(x_1, x_11, x_3, x_4, x_5);
return x_12;
}
case 2:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
lean_dec(x_6);
x_14 = l_Lean_Expr_mvar___override(x_13);
x_15 = lean_apply_4(x_1, x_14, x_3, x_4, x_5);
return x_15;
}
case 3:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_16 = lean_ctor_get(x_6, 0);
lean_inc(x_16);
lean_dec(x_6);
x_17 = l_Lean_Expr_sort___override(x_16);
x_18 = lean_apply_4(x_1, x_17, x_3, x_4, x_5);
return x_18;
}
case 4:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_1);
x_19 = lean_ctor_get(x_6, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_6, 1);
lean_inc(x_20);
lean_dec(x_6);
x_21 = lean_st_ref_get(x_4, x_5);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_19);
x_26 = l_Lean_Compiler_hasMacroInlineAttribute(x_25, x_19);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_21, 0, x_28);
return x_21;
}
else
{
lean_object* x_29; 
lean_free_object(x_21);
x_29 = l_Lean_getConstInfo___at_____private_Lean_Compiler_LCNF_Util_0__Lean_Compiler_LCNF_getCasesOnInductiveVal_x3f_spec__0(x_19, x_3, x_4, x_24);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Core_instantiateValueLevelParams(x_30, x_20, x_3, x_4, x_31);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_30);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_box(0);
x_36 = l_Lean_Expr_sort___override(x_35);
x_37 = l_Lean_Expr_getAppNumArgs(x_2);
lean_inc(x_37);
x_38 = lean_mk_array(x_37, x_36);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_sub(x_37, x_39);
lean_dec(x_37);
x_41 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_38, x_40);
x_42 = l_Lean_Expr_beta(x_34, x_41);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_32, 0, x_43);
return x_32;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_44 = lean_ctor_get(x_32, 0);
x_45 = lean_ctor_get(x_32, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_32);
x_46 = lean_box(0);
x_47 = l_Lean_Expr_sort___override(x_46);
x_48 = l_Lean_Expr_getAppNumArgs(x_2);
lean_inc(x_48);
x_49 = lean_mk_array(x_48, x_47);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_sub(x_48, x_50);
lean_dec(x_48);
x_52 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_49, x_51);
x_53 = l_Lean_Expr_beta(x_44, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_45);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_32);
if (x_56 == 0)
{
return x_32;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_32, 0);
x_58 = lean_ctor_get(x_32, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_32);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_20);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_60 = !lean_is_exclusive(x_29);
if (x_60 == 0)
{
return x_29;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_29, 0);
x_62 = lean_ctor_get(x_29, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_29);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_64 = lean_ctor_get(x_21, 0);
x_65 = lean_ctor_get(x_21, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_21);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
lean_dec(x_64);
lean_inc(x_19);
x_67 = l_Lean_Compiler_hasMacroInlineAttribute(x_66, x_19);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_65);
return x_70;
}
else
{
lean_object* x_71; 
x_71 = l_Lean_getConstInfo___at_____private_Lean_Compiler_LCNF_Util_0__Lean_Compiler_LCNF_getCasesOnInductiveVal_x3f_spec__0(x_19, x_3, x_4, x_65);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = l_Lean_Core_instantiateValueLevelParams(x_72, x_20, x_3, x_4, x_73);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_72);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_77 = x_74;
} else {
 lean_dec_ref(x_74);
 x_77 = lean_box(0);
}
x_78 = lean_box(0);
x_79 = l_Lean_Expr_sort___override(x_78);
x_80 = l_Lean_Expr_getAppNumArgs(x_2);
lean_inc(x_80);
x_81 = lean_mk_array(x_80, x_79);
x_82 = lean_unsigned_to_nat(1u);
x_83 = lean_nat_sub(x_80, x_82);
lean_dec(x_80);
x_84 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_81, x_83);
x_85 = l_Lean_Expr_beta(x_75, x_84);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
if (lean_is_scalar(x_77)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_77;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_76);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_2);
x_88 = lean_ctor_get(x_74, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_74, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_90 = x_74;
} else {
 lean_dec_ref(x_74);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_20);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_92 = lean_ctor_get(x_71, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_71, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_94 = x_71;
} else {
 lean_dec_ref(x_71);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
}
}
case 5:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_2);
x_96 = lean_ctor_get(x_6, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_6, 1);
lean_inc(x_97);
lean_dec(x_6);
x_98 = l_Lean_Expr_app___override(x_96, x_97);
x_99 = lean_apply_4(x_1, x_98, x_3, x_4, x_5);
return x_99;
}
case 6:
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_2);
x_100 = lean_ctor_get(x_6, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_6, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_6, 2);
lean_inc(x_102);
x_103 = lean_ctor_get_uint8(x_6, sizeof(void*)*3 + 8);
lean_dec(x_6);
x_104 = l_Lean_Expr_lam___override(x_100, x_101, x_102, x_103);
x_105 = lean_apply_4(x_1, x_104, x_3, x_4, x_5);
return x_105;
}
case 7:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_2);
x_106 = lean_ctor_get(x_6, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_6, 1);
lean_inc(x_107);
x_108 = lean_ctor_get(x_6, 2);
lean_inc(x_108);
x_109 = lean_ctor_get_uint8(x_6, sizeof(void*)*3 + 8);
lean_dec(x_6);
x_110 = l_Lean_Expr_forallE___override(x_106, x_107, x_108, x_109);
x_111 = lean_apply_4(x_1, x_110, x_3, x_4, x_5);
return x_111;
}
case 8:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_2);
x_112 = lean_ctor_get(x_6, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_6, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_6, 2);
lean_inc(x_114);
x_115 = lean_ctor_get(x_6, 3);
lean_inc(x_115);
x_116 = lean_ctor_get_uint8(x_6, sizeof(void*)*4 + 8);
lean_dec(x_6);
x_117 = l_Lean_Expr_letE___override(x_112, x_113, x_114, x_115, x_116);
x_118 = lean_apply_4(x_1, x_117, x_3, x_4, x_5);
return x_118;
}
case 9:
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_2);
x_119 = lean_ctor_get(x_6, 0);
lean_inc(x_119);
lean_dec(x_6);
x_120 = l_Lean_Expr_lit___override(x_119);
x_121 = lean_apply_4(x_1, x_120, x_3, x_4, x_5);
return x_121;
}
case 10:
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_2);
x_122 = lean_ctor_get(x_6, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_6, 1);
lean_inc(x_123);
lean_dec(x_6);
x_124 = l_Lean_Expr_mdata___override(x_122, x_123);
x_125 = lean_apply_4(x_1, x_124, x_3, x_4, x_5);
return x_125;
}
default: 
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_2);
x_126 = lean_ctor_get(x_6, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_6, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_6, 2);
lean_inc(x_128);
lean_dec(x_6);
x_129 = l_Lean_Expr_proj___override(x_126, x_127, x_128);
x_130 = lean_apply_4(x_1, x_129, x_3, x_4, x_5);
return x_130;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_macroInline___lam__0___boxed), 4, 0);
x_6 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_macroInline___lam__1___boxed), 4, 0);
x_7 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_macroInline___lam__2), 5, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = l_Lean_Core_transform___at___Lean_Core_betaReduce_spec__0(x_1, x_7, x_5, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_macroInline___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_macroInline___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___redArg___lam__0), 7, 1);
lean_closure_set(x_11, 0, x_4);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_withLetDecl___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg___lam__0), 8, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = lean_box(0);
x_11 = lean_box(0);
x_12 = lean_unbox(x_10);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___redArg(x_1, x_12, x_11, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_12 = l_Array_append(lean_box(0), x_1, x_5);
x_13 = l_Lean_mkAppN(x_2, x_5);
x_14 = lean_box(1);
x_15 = lean_unbox(x_14);
x_16 = l_Lean_Meta_mkLambdaFVars(x_12, x_13, x_3, x_4, x_3, x_15, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__1(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_mk_empty_array_with_capacity(x_9);
lean_inc(x_3);
x_11 = lean_array_push(x_10, x_3);
x_12 = l_Lean_Meta_mkLetFVars(x_11, x_3, x_1, x_2, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_3);
x_11 = lean_nat_dec_eq(x_10, x_1);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_box(1);
x_13 = lean_nat_dec_lt(x_1, x_10);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_14 = lean_infer_type(x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(x_11);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__0___boxed), 11, 4);
lean_closure_set(x_18, 0, x_3);
lean_closure_set(x_18, 1, x_2);
lean_closure_set(x_18, 2, x_17);
lean_closure_set(x_18, 3, x_12);
x_19 = lean_nat_sub(x_1, x_10);
lean_dec(x_10);
lean_dec(x_1);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6(lean_box(0), x_15, x_20, x_18, x_11, x_5, x_6, x_7, x_8, x_16);
return x_21;
}
else
{
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; 
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_3);
x_22 = l_Array_toSubarray___redArg(x_3, x_1, x_10);
x_23 = l_Array_ofSubarray___redArg(x_22);
lean_dec(x_22);
x_24 = lean_box(1);
x_25 = lean_unbox(x_12);
x_26 = lean_unbox(x_24);
x_27 = l_Lean_Meta_mkLambdaFVars(x_23, x_4, x_11, x_25, x_11, x_26, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_23);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_mk_string_unchecked("_k", 2, 2);
x_31 = l_Lean_Name_mkStr1(x_30);
x_32 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_31, x_7, x_8, x_29);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_28);
x_35 = lean_infer_type(x_28, x_5, x_6, x_7, x_8, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__1___boxed), 8, 2);
lean_closure_set(x_38, 0, x_12);
lean_closure_set(x_38, 1, x_24);
x_39 = lean_box(0);
x_40 = lean_unbox(x_39);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_41 = l_Lean_Meta_withLetDecl___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___redArg(x_33, x_36, x_28, x_38, x_40, x_5, x_6, x_7, x_8, x_37);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; lean_object* x_49; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_unsigned_to_nat(0u);
x_45 = l_Array_toSubarray___redArg(x_3, x_44, x_1);
x_46 = l_Array_ofSubarray___redArg(x_45);
lean_dec(x_45);
x_47 = lean_unbox(x_12);
x_48 = lean_unbox(x_24);
x_49 = l_Lean_Meta_mkLambdaFVars(x_46, x_42, x_11, x_47, x_11, x_48, x_5, x_6, x_7, x_8, x_43);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_46);
return x_49;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_41;
}
}
else
{
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_35;
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_27;
}
}
}
else
{
lean_object* x_50; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_2);
lean_ctor_set(x_50, 1, x_9);
return x_50;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__2), 9, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_1);
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
x_11 = l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg(x_1, x_8, x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l_Lean_Meta_withLetDecl___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___redArg(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_6);
lean_dec(x_6);
x_13 = l_Lean_Meta_withLetDecl___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0(x_1, x_2, x_3, x_4, x_5, x_12, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__0(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__1(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_1, x_14);
lean_inc(x_8);
x_16 = lean_array_set(x_2, x_3, x_8);
x_17 = lean_array_push(x_4, x_8);
x_18 = l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher(x_5, x_6, x_7, x_15, x_16, x_17, x_9, x_10, x_11, x_12, x_13);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_3);
x_13 = lean_nat_dec_lt(x_4, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_3);
x_14 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Core_instantiateValueLevelParams(x_15, x_2, x_9, x_10, x_16);
lean_dec(x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Expr_beta(x_18, x_5);
x_21 = lean_box(1);
x_22 = lean_box(1);
x_23 = lean_unbox(x_21);
x_24 = lean_unbox(x_22);
x_25 = l_Lean_Meta_mkLetFVars(x_6, x_20, x_23, x_24, x_7, x_8, x_9, x_10, x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_25;
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_17;
}
}
else
{
uint8_t x_26; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_14);
if (x_26 == 0)
{
return x_14;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_14, 0);
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_14);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_3, 2);
lean_inc(x_30);
x_31 = l_Lean_Meta_Match_MatcherInfo_getFirstAltPos(x_3);
x_32 = lean_nat_add(x_4, x_31);
lean_dec(x_31);
x_33 = lean_array_fget(x_30, x_4);
lean_dec(x_30);
x_34 = l_Lean_instInhabitedExpr;
x_35 = lean_array_get(x_34, x_5, x_32);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_36 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt(x_35, x_33, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_mk_string_unchecked("_alt", 4, 4);
x_40 = l_Lean_Name_mkStr1(x_39);
x_41 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_40, x_9, x_10, x_38);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_37);
x_44 = lean_infer_type(x_37, x_7, x_8, x_9, x_10, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___lam__0___boxed), 13, 7);
lean_closure_set(x_47, 0, x_4);
lean_closure_set(x_47, 1, x_5);
lean_closure_set(x_47, 2, x_32);
lean_closure_set(x_47, 3, x_6);
lean_closure_set(x_47, 4, x_1);
lean_closure_set(x_47, 5, x_2);
lean_closure_set(x_47, 6, x_3);
x_48 = lean_box(0);
x_49 = lean_unbox(x_48);
x_50 = l_Lean_Meta_withLetDecl___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___redArg(x_42, x_45, x_37, x_47, x_49, x_7, x_8, x_9, x_10, x_46);
return x_50;
}
else
{
lean_dec(x_42);
lean_dec(x_37);
lean_dec(x_32);
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
return x_44;
}
}
else
{
lean_dec(x_32);
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
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lam__2(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = l_Lean_mkAppN(x_1, x_4);
x_12 = lean_box(1);
x_13 = lean_unbox(x_12);
x_14 = l_Lean_Meta_mkLambdaFVars(x_4, x_11, x_2, x_3, x_2, x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Expr_getAppFn(x_2);
switch (lean_obj_tag(x_8)) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Expr_bvar___override(x_9);
x_11 = lean_apply_6(x_1, x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = l_Lean_Expr_fvar___override(x_12);
x_14 = lean_apply_6(x_1, x_13, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
case 2:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
x_16 = l_Lean_Expr_mvar___override(x_15);
x_17 = lean_apply_6(x_1, x_16, x_3, x_4, x_5, x_6, x_7);
return x_17;
}
case 3:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_18 = lean_ctor_get(x_8, 0);
lean_inc(x_18);
lean_dec(x_8);
x_19 = l_Lean_Expr_sort___override(x_18);
x_20 = lean_apply_6(x_1, x_19, x_3, x_4, x_5, x_6, x_7);
return x_20;
}
case 4:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_1);
x_21 = lean_ctor_get(x_8, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_dec(x_8);
lean_inc(x_21);
x_23 = l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_reduceMatcher_x3f_spec__0___redArg(x_21, x_6, x_7);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_23, 0, x_28);
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_23);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_23, 1);
x_35 = lean_ctor_get(x_23, 0);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_24);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_24, 0);
x_38 = l_Lean_Expr_getAppNumArgs(x_2);
x_39 = l_Lean_Meta_Match_MatcherInfo_arity(x_37);
x_40 = lean_nat_dec_lt(x_39, x_38);
if (x_40 == 0)
{
uint8_t x_41; 
lean_free_object(x_23);
x_41 = lean_nat_dec_lt(x_38, x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_39);
lean_free_object(x_24);
x_42 = lean_box(0);
x_43 = l_Lean_Expr_sort___override(x_42);
lean_inc(x_38);
x_44 = lean_mk_array(x_38, x_43);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_sub(x_38, x_45);
lean_dec(x_38);
x_47 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_44, x_46);
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_mk_empty_array_with_capacity(x_48);
x_50 = l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher(x_21, x_22, x_37, x_48, x_47, x_49, x_3, x_4, x_5, x_6, x_34);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_50, 0, x_53);
return x_50;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_50, 0);
x_55 = lean_ctor_get(x_50, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_50);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_54);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_50);
if (x_58 == 0)
{
return x_50;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_50, 0);
x_60 = lean_ctor_get(x_50, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_50);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; 
lean_dec(x_37);
lean_dec(x_22);
lean_dec(x_21);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_62 = lean_infer_type(x_2, x_3, x_4, x_5, x_6, x_34);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_box(x_40);
x_66 = lean_box(x_41);
x_67 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_inlineMatchers___lam__2___boxed), 10, 3);
lean_closure_set(x_67, 0, x_2);
lean_closure_set(x_67, 1, x_65);
lean_closure_set(x_67, 2, x_66);
x_68 = lean_nat_sub(x_39, x_38);
lean_dec(x_38);
lean_dec(x_39);
lean_ctor_set(x_24, 0, x_68);
x_69 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6(lean_box(0), x_63, x_24, x_67, x_40, x_3, x_4, x_5, x_6, x_64);
return x_69;
}
else
{
uint8_t x_70; 
lean_dec(x_39);
lean_dec(x_38);
lean_free_object(x_24);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_70 = !lean_is_exclusive(x_62);
if (x_70 == 0)
{
return x_62;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_62, 0);
x_72 = lean_ctor_get(x_62, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_62);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_39);
lean_dec(x_38);
lean_free_object(x_24);
lean_dec(x_37);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_23, 0, x_75);
return x_23;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_76 = lean_ctor_get(x_24, 0);
lean_inc(x_76);
lean_dec(x_24);
x_77 = l_Lean_Expr_getAppNumArgs(x_2);
x_78 = l_Lean_Meta_Match_MatcherInfo_arity(x_76);
x_79 = lean_nat_dec_lt(x_78, x_77);
if (x_79 == 0)
{
uint8_t x_80; 
lean_free_object(x_23);
x_80 = lean_nat_dec_lt(x_77, x_78);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_78);
x_81 = lean_box(0);
x_82 = l_Lean_Expr_sort___override(x_81);
lean_inc(x_77);
x_83 = lean_mk_array(x_77, x_82);
x_84 = lean_unsigned_to_nat(1u);
x_85 = lean_nat_sub(x_77, x_84);
lean_dec(x_77);
x_86 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_83, x_85);
x_87 = lean_unsigned_to_nat(0u);
x_88 = lean_mk_empty_array_with_capacity(x_87);
x_89 = l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher(x_21, x_22, x_76, x_87, x_86, x_88, x_3, x_4, x_5, x_6, x_34);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
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
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_90);
if (lean_is_scalar(x_92)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_92;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_91);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_89, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_89, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_97 = x_89;
} else {
 lean_dec_ref(x_89);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
else
{
lean_object* x_99; 
lean_dec(x_76);
lean_dec(x_22);
lean_dec(x_21);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_99 = lean_infer_type(x_2, x_3, x_4, x_5, x_6, x_34);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_box(x_79);
x_103 = lean_box(x_80);
x_104 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_inlineMatchers___lam__2___boxed), 10, 3);
lean_closure_set(x_104, 0, x_2);
lean_closure_set(x_104, 1, x_102);
lean_closure_set(x_104, 2, x_103);
x_105 = lean_nat_sub(x_78, x_77);
lean_dec(x_77);
lean_dec(x_78);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
x_107 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6(lean_box(0), x_100, x_106, x_104, x_79, x_3, x_4, x_5, x_6, x_101);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_108 = lean_ctor_get(x_99, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_99, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_110 = x_99;
} else {
 lean_dec_ref(x_99);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_112 = lean_box(0);
x_113 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_23, 0, x_113);
return x_23;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_114 = lean_ctor_get(x_23, 1);
lean_inc(x_114);
lean_dec(x_23);
x_115 = lean_ctor_get(x_24, 0);
lean_inc(x_115);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 x_116 = x_24;
} else {
 lean_dec_ref(x_24);
 x_116 = lean_box(0);
}
x_117 = l_Lean_Expr_getAppNumArgs(x_2);
x_118 = l_Lean_Meta_Match_MatcherInfo_arity(x_115);
x_119 = lean_nat_dec_lt(x_118, x_117);
if (x_119 == 0)
{
uint8_t x_120; 
x_120 = lean_nat_dec_lt(x_117, x_118);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_118);
lean_dec(x_116);
x_121 = lean_box(0);
x_122 = l_Lean_Expr_sort___override(x_121);
lean_inc(x_117);
x_123 = lean_mk_array(x_117, x_122);
x_124 = lean_unsigned_to_nat(1u);
x_125 = lean_nat_sub(x_117, x_124);
lean_dec(x_117);
x_126 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_123, x_125);
x_127 = lean_unsigned_to_nat(0u);
x_128 = lean_mk_empty_array_with_capacity(x_127);
x_129 = l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher(x_21, x_22, x_115, x_127, x_126, x_128, x_3, x_4, x_5, x_6, x_114);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
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
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_130);
if (lean_is_scalar(x_132)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_132;
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_131);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_135 = lean_ctor_get(x_129, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_129, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_137 = x_129;
} else {
 lean_dec_ref(x_129);
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
}
else
{
lean_object* x_139; 
lean_dec(x_115);
lean_dec(x_22);
lean_dec(x_21);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_139 = lean_infer_type(x_2, x_3, x_4, x_5, x_6, x_114);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_142 = lean_box(x_119);
x_143 = lean_box(x_120);
x_144 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_inlineMatchers___lam__2___boxed), 10, 3);
lean_closure_set(x_144, 0, x_2);
lean_closure_set(x_144, 1, x_142);
lean_closure_set(x_144, 2, x_143);
x_145 = lean_nat_sub(x_118, x_117);
lean_dec(x_117);
lean_dec(x_118);
if (lean_is_scalar(x_116)) {
 x_146 = lean_alloc_ctor(1, 1, 0);
} else {
 x_146 = x_116;
}
lean_ctor_set(x_146, 0, x_145);
x_147 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6(lean_box(0), x_140, x_146, x_144, x_119, x_3, x_4, x_5, x_6, x_141);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_148 = lean_ctor_get(x_139, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_139, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_150 = x_139;
} else {
 lean_dec_ref(x_139);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_152 = lean_box(0);
x_153 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_153, 0, x_152);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_114);
return x_154;
}
}
}
}
case 5:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_2);
x_155 = lean_ctor_get(x_8, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_8, 1);
lean_inc(x_156);
lean_dec(x_8);
x_157 = l_Lean_Expr_app___override(x_155, x_156);
x_158 = lean_apply_6(x_1, x_157, x_3, x_4, x_5, x_6, x_7);
return x_158;
}
case 6:
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_2);
x_159 = lean_ctor_get(x_8, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_8, 1);
lean_inc(x_160);
x_161 = lean_ctor_get(x_8, 2);
lean_inc(x_161);
x_162 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 8);
lean_dec(x_8);
x_163 = l_Lean_Expr_lam___override(x_159, x_160, x_161, x_162);
x_164 = lean_apply_6(x_1, x_163, x_3, x_4, x_5, x_6, x_7);
return x_164;
}
case 7:
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_2);
x_165 = lean_ctor_get(x_8, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_8, 1);
lean_inc(x_166);
x_167 = lean_ctor_get(x_8, 2);
lean_inc(x_167);
x_168 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 8);
lean_dec(x_8);
x_169 = l_Lean_Expr_forallE___override(x_165, x_166, x_167, x_168);
x_170 = lean_apply_6(x_1, x_169, x_3, x_4, x_5, x_6, x_7);
return x_170;
}
case 8:
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_2);
x_171 = lean_ctor_get(x_8, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_8, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_8, 2);
lean_inc(x_173);
x_174 = lean_ctor_get(x_8, 3);
lean_inc(x_174);
x_175 = lean_ctor_get_uint8(x_8, sizeof(void*)*4 + 8);
lean_dec(x_8);
x_176 = l_Lean_Expr_letE___override(x_171, x_172, x_173, x_174, x_175);
x_177 = lean_apply_6(x_1, x_176, x_3, x_4, x_5, x_6, x_7);
return x_177;
}
case 9:
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_2);
x_178 = lean_ctor_get(x_8, 0);
lean_inc(x_178);
lean_dec(x_8);
x_179 = l_Lean_Expr_lit___override(x_178);
x_180 = lean_apply_6(x_1, x_179, x_3, x_4, x_5, x_6, x_7);
return x_180;
}
case 10:
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_2);
x_181 = lean_ctor_get(x_8, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_8, 1);
lean_inc(x_182);
lean_dec(x_8);
x_183 = l_Lean_Expr_mdata___override(x_181, x_182);
x_184 = lean_apply_6(x_1, x_183, x_3, x_4, x_5, x_6, x_7);
return x_184;
}
default: 
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_2);
x_185 = lean_ctor_get(x_8, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_8, 1);
lean_inc(x_186);
x_187 = lean_ctor_get(x_8, 2);
lean_inc(x_187);
lean_dec(x_8);
x_188 = l_Lean_Expr_proj___override(x_185, x_186, x_187);
x_189 = lean_apply_6(x_1, x_188, x_3, x_4, x_5, x_6, x_7);
return x_189;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint64_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; lean_object* x_77; 
x_5 = lean_box(0);
x_6 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_7 = lean_unsigned_to_nat(2u);
x_8 = lean_unsigned_to_nat(5u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_to_nat(x_9);
x_11 = lean_nat_pow(x_7, x_10);
lean_dec(x_10);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = lean_usize_to_nat(x_12);
x_14 = lean_mk_empty_array_with_capacity(x_13);
lean_dec(x_13);
lean_inc(x_14);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_unsigned_to_nat(0u);
lean_inc(x_6);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_6);
lean_inc(x_6);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_6);
lean_inc(x_6);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_6);
lean_inc(x_6);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_6);
lean_inc(x_6);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_6);
lean_inc(x_6);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_6);
lean_inc(x_17);
x_23 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_16);
lean_ctor_set(x_23, 2, x_16);
lean_ctor_set(x_23, 3, x_17);
lean_ctor_set(x_23, 4, x_18);
lean_ctor_set(x_23, 5, x_19);
lean_ctor_set(x_23, 6, x_20);
lean_ctor_set(x_23, 7, x_21);
lean_ctor_set(x_23, 8, x_22);
lean_inc(x_6);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_6);
lean_inc(x_6);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_6);
lean_inc(x_6);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_6);
lean_inc(x_6);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_6);
lean_inc(x_27);
lean_inc(x_24);
x_28 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_25);
lean_ctor_set(x_28, 2, x_26);
lean_ctor_set(x_28, 3, x_24);
lean_ctor_set(x_28, 4, x_27);
lean_ctor_set(x_28, 5, x_27);
lean_inc(x_14);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_14);
lean_inc(x_14);
x_30 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_14);
lean_ctor_set(x_30, 2, x_16);
lean_ctor_set(x_30, 3, x_16);
lean_ctor_set_usize(x_30, 4, x_9);
lean_inc(x_6);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_6);
lean_inc_n(x_17, 2);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_17);
lean_ctor_set(x_32, 1, x_17);
lean_ctor_set(x_32, 2, x_17);
lean_ctor_set(x_32, 3, x_31);
x_33 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_33, 0, x_23);
lean_ctor_set(x_33, 1, x_28);
lean_ctor_set(x_33, 2, x_5);
lean_ctor_set(x_33, 3, x_30);
lean_ctor_set(x_33, 4, x_32);
x_34 = lean_st_mk_ref(x_33, x_4);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_inlineMatchers___lam__0___boxed), 6, 0);
x_38 = lean_box(1);
x_39 = lean_box(1);
x_40 = lean_box(0);
x_41 = lean_box(2);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_6);
x_43 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_43, 0, x_15);
lean_ctor_set(x_43, 1, x_14);
lean_ctor_set(x_43, 2, x_16);
lean_ctor_set(x_43, 3, x_16);
lean_ctor_set_usize(x_43, 4, x_9);
x_44 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_inlineMatchers___lam__1___boxed), 6, 0);
x_45 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_inlineMatchers___lam__3), 7, 1);
lean_closure_set(x_45, 0, x_37);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 0, 18);
x_48 = lean_unbox(x_46);
lean_ctor_set_uint8(x_47, 0, x_48);
x_49 = lean_unbox(x_46);
lean_ctor_set_uint8(x_47, 1, x_49);
x_50 = lean_unbox(x_46);
lean_ctor_set_uint8(x_47, 2, x_50);
x_51 = lean_unbox(x_46);
lean_ctor_set_uint8(x_47, 3, x_51);
x_52 = lean_unbox(x_46);
lean_ctor_set_uint8(x_47, 4, x_52);
x_53 = lean_unbox(x_38);
lean_ctor_set_uint8(x_47, 5, x_53);
x_54 = lean_unbox(x_38);
lean_ctor_set_uint8(x_47, 6, x_54);
x_55 = lean_unbox(x_46);
lean_ctor_set_uint8(x_47, 7, x_55);
x_56 = lean_unbox(x_38);
lean_ctor_set_uint8(x_47, 8, x_56);
x_57 = lean_unbox(x_39);
lean_ctor_set_uint8(x_47, 9, x_57);
x_58 = lean_unbox(x_40);
lean_ctor_set_uint8(x_47, 10, x_58);
x_59 = lean_unbox(x_38);
lean_ctor_set_uint8(x_47, 11, x_59);
x_60 = lean_unbox(x_38);
lean_ctor_set_uint8(x_47, 12, x_60);
x_61 = lean_unbox(x_38);
lean_ctor_set_uint8(x_47, 13, x_61);
x_62 = lean_unbox(x_41);
lean_ctor_set_uint8(x_47, 14, x_62);
x_63 = lean_unbox(x_38);
lean_ctor_set_uint8(x_47, 15, x_63);
x_64 = lean_unbox(x_38);
lean_ctor_set_uint8(x_47, 16, x_64);
x_65 = lean_unbox(x_38);
lean_ctor_set_uint8(x_47, 17, x_65);
x_66 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_47);
x_67 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_67, 0, x_42);
lean_ctor_set(x_67, 1, x_43);
lean_ctor_set(x_67, 2, x_5);
x_68 = lean_mk_empty_array_with_capacity(x_16);
x_69 = lean_box(0);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_71, 0, x_47);
lean_ctor_set(x_71, 1, x_5);
lean_ctor_set(x_71, 2, x_67);
lean_ctor_set(x_71, 3, x_68);
lean_ctor_set(x_71, 4, x_69);
lean_ctor_set(x_71, 5, x_16);
lean_ctor_set(x_71, 6, x_70);
lean_ctor_set_uint64(x_71, sizeof(void*)*7, x_66);
x_72 = lean_unbox(x_46);
lean_ctor_set_uint8(x_71, sizeof(void*)*7 + 8, x_72);
x_73 = lean_unbox(x_46);
lean_ctor_set_uint8(x_71, sizeof(void*)*7 + 9, x_73);
x_74 = lean_unbox(x_46);
lean_ctor_set_uint8(x_71, sizeof(void*)*7 + 10, x_74);
x_75 = lean_unbox(x_46);
x_76 = lean_unbox(x_46);
lean_inc(x_35);
x_77 = l_Lean_Meta_transform___at___Lean_Meta_zetaReduce_spec__0(x_1, x_45, x_44, x_75, x_76, x_71, x_35, x_2, x_3, x_36);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_st_ref_get(x_35, x_79);
lean_dec(x_35);
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_80, 0);
lean_dec(x_82);
lean_ctor_set(x_80, 0, x_78);
return x_80;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_78);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
else
{
lean_dec(x_35);
return x_77;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_inlineMatchers___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_inlineMatchers___lam__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l_Lean_Compiler_LCNF_inlineMatchers___lam__2(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_is_unsafe_rec_name(x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = l_Lean_Expr_const___override(x_11, x_6);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 0, x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
lean_dec(x_7);
x_15 = l_Lean_Expr_const___override(x_14, x_6);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
return x_17;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_4);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___lam__0___boxed), 4, 0);
x_6 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_macroInline___lam__0___boxed), 4, 0);
x_7 = l_Lean_Core_transform___at___Lean_Core_betaReduce_spec__0(x_1, x_5, x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
lean_inc(x_1);
x_8 = lean_mk_unsafe_rec_name(x_1);
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
lean_inc(x_7);
x_11 = l_Lean_Environment_find_x3f(x_7, x_8, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_9);
x_13 = l_Lean_Environment_find_x3f(x_7, x_1, x_12);
lean_ctor_set(x_4, 0, x_13);
return x_4;
}
else
{
lean_dec(x_7);
lean_dec(x_1);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_4);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_1);
x_17 = lean_mk_unsafe_rec_name(x_1);
x_18 = lean_box(0);
x_19 = lean_unbox(x_18);
lean_inc(x_16);
x_20 = l_Lean_Environment_find_x3f(x_16, x_17, x_19);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_unbox(x_18);
x_22 = l_Lean_Environment_find_x3f(x_16, x_1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_15);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_16);
lean_dec(x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_15);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_getDeclInfo_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Compiler_LCNF_toDecl_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 7)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 2);
lean_inc(x_11);
lean_dec(x_7);
lean_inc(x_10);
x_12 = lean_is_marked_borrowed(x_10);
x_13 = l_Lean_Compiler_LCNF_mkParam(x_9, x_10, x_12, x_2, x_3, x_4, x_5, x_6);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_array_push(x_8, x_15);
lean_ctor_set(x_13, 1, x_17);
lean_ctor_set(x_13, 0, x_11);
x_1 = x_13;
x_6 = x_16;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_array_push(x_8, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_21);
x_1 = x_22;
x_6 = x_20;
goto _start;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_7);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_6);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_mk_empty_array_with_capacity(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Loop_forIn_loop___at___Lean_Compiler_LCNF_toDecl_spec__0(x_9, x_2, x_3, x_4, x_5, x_6);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__1(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_10 = l_Lean_Meta_etaExpand(x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(1);
x_14 = lean_unbox(x_13);
x_15 = l_Lean_Meta_mkLambdaFVars(x_3, x_11, x_1, x_2, x_1, x_14, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_15;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; uint8_t x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_901; lean_object* x_932; 
lean_inc(x_1);
x_932 = lean_is_unsafe_rec_name(x_1);
if (lean_obj_tag(x_932) == 0)
{
x_901 = x_1;
goto block_931;
}
else
{
lean_object* x_933; 
lean_dec(x_1);
x_933 = lean_ctor_get(x_932, 0);
lean_inc(x_933);
lean_dec(x_932);
x_901 = x_933;
goto block_931;
}
block_25:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = l_Lean_ConstantInfo_levelParams(x_10);
lean_dec(x_10);
x_21 = lean_mk_empty_array_with_capacity(x_8);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_9);
x_23 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_23, 0, x_13);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set(x_23, 2, x_14);
lean_ctor_set(x_23, 3, x_21);
lean_ctor_set(x_23, 4, x_22);
lean_ctor_set(x_23, 5, x_11);
lean_ctor_set_uint8(x_23, sizeof(void*)*6, x_12);
lean_ctor_set_uint8(x_23, sizeof(void*)*6 + 1, x_7);
x_24 = l_Lean_Compiler_LCNF_Decl_etaExpand(x_23, x_15, x_16, x_17, x_18, x_19);
return x_24;
}
block_46:
{
lean_object* x_34; uint8_t x_35; 
lean_inc(x_32);
x_34 = l_Lean_Compiler_LCNF_toDecl___lam__0(x_32, x_2, x_3, x_4, x_5, x_33);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = l_Lean_ConstantInfo_levelParams(x_28);
lean_dec(x_28);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_27);
x_39 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_39, 0, x_30);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set(x_39, 2, x_32);
lean_ctor_set(x_39, 3, x_36);
lean_ctor_set(x_39, 4, x_38);
lean_ctor_set(x_39, 5, x_29);
lean_ctor_set_uint8(x_39, sizeof(void*)*6, x_31);
lean_ctor_set_uint8(x_39, sizeof(void*)*6 + 1, x_26);
lean_ctor_set(x_34, 0, x_39);
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_34, 0);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_34);
x_42 = l_Lean_ConstantInfo_levelParams(x_28);
lean_dec(x_28);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_27);
x_44 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_44, 0, x_30);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set(x_44, 2, x_32);
lean_ctor_set(x_44, 3, x_40);
lean_ctor_set(x_44, 4, x_43);
lean_ctor_set(x_44, 5, x_29);
lean_ctor_set_uint8(x_44, sizeof(void*)*6, x_31);
lean_ctor_set_uint8(x_44, sizeof(void*)*6 + 1, x_26);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_41);
return x_45;
}
}
block_72:
{
lean_object* x_54; uint8_t x_55; 
lean_inc(x_52);
x_54 = l_Lean_Compiler_LCNF_toDecl___lam__0(x_52, x_2, x_3, x_4, x_5, x_53);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = l_Lean_ConstantInfo_levelParams(x_49);
lean_dec(x_49);
x_58 = lean_box(0);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_62, 0, x_51);
lean_ctor_set(x_62, 1, x_57);
lean_ctor_set(x_62, 2, x_52);
lean_ctor_set(x_62, 3, x_56);
lean_ctor_set(x_62, 4, x_61);
lean_ctor_set(x_62, 5, x_50);
lean_ctor_set_uint8(x_62, sizeof(void*)*6, x_48);
lean_ctor_set_uint8(x_62, sizeof(void*)*6 + 1, x_47);
lean_ctor_set(x_54, 0, x_62);
return x_54;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_63 = lean_ctor_get(x_54, 0);
x_64 = lean_ctor_get(x_54, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_54);
x_65 = l_Lean_ConstantInfo_levelParams(x_49);
lean_dec(x_49);
x_66 = lean_box(0);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_70, 0, x_51);
lean_ctor_set(x_70, 1, x_65);
lean_ctor_set(x_70, 2, x_52);
lean_ctor_set(x_70, 3, x_63);
lean_ctor_set(x_70, 4, x_69);
lean_ctor_set(x_70, 5, x_50);
lean_ctor_set_uint8(x_70, sizeof(void*)*6, x_48);
lean_ctor_set_uint8(x_70, sizeof(void*)*6 + 1, x_47);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_64);
return x_71;
}
}
block_900:
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_st_ref_get(x_5, x_75);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_79 = lean_ctor_get(x_77, 0);
x_80 = lean_ctor_get(x_77, 1);
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
lean_dec(x_79);
lean_inc(x_74);
lean_inc(x_81);
x_82 = l_Lean_Compiler_getInlineAttribute_x3f(x_81, x_74);
lean_inc(x_74);
lean_inc(x_81);
x_83 = lean_get_extern_attr_data(x_81, x_74);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; lean_object* x_85; 
lean_inc(x_74);
x_84 = l_Lean_hasInitAttr(x_81, x_74);
x_85 = lean_box(1);
if (x_84 == 0)
{
uint8_t x_86; lean_object* x_87; 
x_86 = lean_unbox(x_85);
lean_inc(x_73);
x_87 = l_Lean_ConstantInfo_value_x3f(x_73, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_82);
lean_dec(x_73);
x_88 = lean_mk_string_unchecked("declaration `", 13, 13);
x_89 = l_Lean_stringToMessageData(x_88);
lean_dec(x_88);
x_90 = l_Lean_MessageData_ofName(x_74);
lean_ctor_set_tag(x_77, 7);
lean_ctor_set(x_77, 1, x_90);
lean_ctor_set(x_77, 0, x_89);
x_91 = lean_mk_string_unchecked("` does not have a value", 23, 23);
x_92 = l_Lean_stringToMessageData(x_91);
lean_dec(x_91);
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_77);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Lean_throwError___at___Lean_Compiler_LCNF_getType_spec__1(lean_box(0), x_93, x_2, x_3, x_4, x_5, x_80);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_94;
}
else
{
uint8_t x_95; 
lean_free_object(x_77);
x_95 = !lean_is_exclusive(x_87);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; size_t x_101; lean_object* x_102; lean_object* x_103; size_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; uint8_t x_135; uint8_t x_136; uint8_t x_137; uint8_t x_138; uint8_t x_139; uint8_t x_140; uint8_t x_141; uint8_t x_142; uint8_t x_143; uint8_t x_144; uint8_t x_145; uint64_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_96 = lean_ctor_get(x_87, 0);
x_97 = lean_box(0);
x_98 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_99 = lean_unsigned_to_nat(2u);
x_100 = lean_unsigned_to_nat(5u);
x_101 = lean_usize_of_nat(x_100);
x_102 = lean_usize_to_nat(x_101);
x_103 = lean_nat_pow(x_99, x_102);
lean_dec(x_102);
x_104 = lean_usize_of_nat(x_103);
lean_dec(x_103);
x_105 = lean_usize_to_nat(x_104);
x_106 = lean_mk_empty_array_with_capacity(x_105);
lean_dec(x_105);
lean_inc(x_106);
lean_ctor_set_tag(x_87, 0);
lean_ctor_set(x_87, 0, x_106);
x_107 = lean_unsigned_to_nat(0u);
lean_inc(x_98);
x_108 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_108, 0, x_98);
lean_inc(x_98);
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_98);
lean_inc(x_98);
x_110 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_110, 0, x_98);
lean_inc(x_98);
x_111 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_111, 0, x_98);
lean_inc(x_98);
x_112 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_112, 0, x_98);
lean_inc(x_98);
x_113 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_113, 0, x_98);
lean_inc(x_108);
x_114 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_114, 0, x_107);
lean_ctor_set(x_114, 1, x_107);
lean_ctor_set(x_114, 2, x_107);
lean_ctor_set(x_114, 3, x_108);
lean_ctor_set(x_114, 4, x_109);
lean_ctor_set(x_114, 5, x_110);
lean_ctor_set(x_114, 6, x_111);
lean_ctor_set(x_114, 7, x_112);
lean_ctor_set(x_114, 8, x_113);
lean_inc(x_98);
x_115 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_115, 0, x_98);
lean_inc(x_98);
x_116 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_116, 0, x_98);
lean_inc(x_98);
x_117 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_117, 0, x_98);
lean_inc(x_98);
x_118 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_118, 0, x_98);
lean_inc(x_118);
lean_inc(x_115);
x_119 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_119, 0, x_115);
lean_ctor_set(x_119, 1, x_116);
lean_ctor_set(x_119, 2, x_117);
lean_ctor_set(x_119, 3, x_115);
lean_ctor_set(x_119, 4, x_118);
lean_ctor_set(x_119, 5, x_118);
lean_inc(x_106);
x_120 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_120, 0, x_106);
lean_inc(x_106);
x_121 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_106);
lean_ctor_set(x_121, 2, x_107);
lean_ctor_set(x_121, 3, x_107);
lean_ctor_set_usize(x_121, 4, x_101);
lean_inc(x_98);
x_122 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_122, 0, x_98);
lean_inc_n(x_108, 2);
x_123 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_123, 0, x_108);
lean_ctor_set(x_123, 1, x_108);
lean_ctor_set(x_123, 2, x_108);
lean_ctor_set(x_123, 3, x_122);
x_124 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_124, 0, x_114);
lean_ctor_set(x_124, 1, x_119);
lean_ctor_set(x_124, 2, x_97);
lean_ctor_set(x_124, 3, x_121);
lean_ctor_set(x_124, 4, x_123);
x_125 = lean_st_mk_ref(x_124, x_80);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = lean_box(1);
x_129 = lean_box(0);
x_130 = lean_box(2);
x_131 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_131, 0, x_98);
x_132 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_132, 0, x_87);
lean_ctor_set(x_132, 1, x_106);
lean_ctor_set(x_132, 2, x_107);
lean_ctor_set(x_132, 3, x_107);
lean_ctor_set_usize(x_132, 4, x_101);
x_133 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_133, 0, x_84);
lean_ctor_set_uint8(x_133, 1, x_84);
lean_ctor_set_uint8(x_133, 2, x_84);
lean_ctor_set_uint8(x_133, 3, x_84);
lean_ctor_set_uint8(x_133, 4, x_84);
x_134 = lean_unbox(x_85);
lean_ctor_set_uint8(x_133, 5, x_134);
x_135 = lean_unbox(x_85);
lean_ctor_set_uint8(x_133, 6, x_135);
lean_ctor_set_uint8(x_133, 7, x_84);
x_136 = lean_unbox(x_85);
lean_ctor_set_uint8(x_133, 8, x_136);
x_137 = lean_unbox(x_128);
lean_ctor_set_uint8(x_133, 9, x_137);
x_138 = lean_unbox(x_129);
lean_ctor_set_uint8(x_133, 10, x_138);
x_139 = lean_unbox(x_85);
lean_ctor_set_uint8(x_133, 11, x_139);
x_140 = lean_unbox(x_85);
lean_ctor_set_uint8(x_133, 12, x_140);
x_141 = lean_unbox(x_85);
lean_ctor_set_uint8(x_133, 13, x_141);
x_142 = lean_unbox(x_130);
lean_ctor_set_uint8(x_133, 14, x_142);
x_143 = lean_unbox(x_85);
lean_ctor_set_uint8(x_133, 15, x_143);
x_144 = lean_unbox(x_85);
lean_ctor_set_uint8(x_133, 16, x_144);
x_145 = lean_unbox(x_85);
lean_ctor_set_uint8(x_133, 17, x_145);
x_146 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_133);
x_147 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_147, 0, x_131);
lean_ctor_set(x_147, 1, x_132);
lean_ctor_set(x_147, 2, x_97);
x_148 = lean_mk_empty_array_with_capacity(x_107);
x_149 = lean_box(0);
x_150 = lean_box(0);
x_151 = l_Lean_ConstantInfo_type(x_73);
x_152 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_152, 0, x_133);
lean_ctor_set(x_152, 1, x_97);
lean_ctor_set(x_152, 2, x_147);
lean_ctor_set(x_152, 3, x_148);
lean_ctor_set(x_152, 4, x_149);
lean_ctor_set(x_152, 5, x_107);
lean_ctor_set(x_152, 6, x_150);
lean_ctor_set_uint64(x_152, sizeof(void*)*7, x_146);
lean_ctor_set_uint8(x_152, sizeof(void*)*7 + 8, x_84);
lean_ctor_set_uint8(x_152, sizeof(void*)*7 + 9, x_84);
lean_ctor_set_uint8(x_152, sizeof(void*)*7 + 10, x_84);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_126);
lean_inc(x_152);
x_153 = l_Lean_Compiler_LCNF_toLCNFType(x_151, x_152, x_126, x_4, x_5, x_127);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_156 = lean_box(x_84);
x_157 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_toDecl___lam__1___boxed), 9, 2);
lean_closure_set(x_157, 0, x_156);
lean_closure_set(x_157, 1, x_85);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_126);
x_158 = l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg(x_96, x_157, x_84, x_152, x_126, x_4, x_5, x_155);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
lean_inc(x_5);
lean_inc(x_4);
x_161 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames(x_159, x_4, x_5, x_160);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
lean_inc(x_5);
lean_inc(x_4);
x_164 = l_Lean_Compiler_LCNF_macroInline(x_162, x_4, x_5, x_163);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
lean_inc(x_5);
lean_inc(x_4);
x_167 = l_Lean_Compiler_LCNF_inlineMatchers(x_165, x_4, x_5, x_166);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
lean_inc(x_5);
lean_inc(x_4);
x_170 = l_Lean_Compiler_LCNF_macroInline(x_168, x_4, x_5, x_169);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_st_ref_get(x_126, x_172);
lean_dec(x_126);
x_174 = lean_ctor_get(x_173, 1);
lean_inc(x_174);
lean_dec(x_173);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_175 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF(x_171, x_2, x_3, x_4, x_5, x_174);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
if (lean_obj_tag(x_176) == 1)
{
lean_object* x_177; 
x_177 = lean_ctor_get(x_176, 1);
lean_inc(x_177);
if (lean_obj_tag(x_177) == 5)
{
lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_178 = lean_ctor_get(x_175, 1);
lean_inc(x_178);
lean_dec(x_175);
x_179 = lean_ctor_get(x_176, 0);
lean_inc(x_179);
lean_dec(x_176);
x_180 = !lean_is_exclusive(x_177);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_181 = lean_ctor_get(x_177, 0);
lean_dec(x_181);
x_182 = l_Lean_Compiler_LCNF_eraseFunDecl(x_179, x_84, x_2, x_3, x_4, x_5, x_178);
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
lean_dec(x_182);
x_184 = l_Lean_ConstantInfo_levelParams(x_73);
lean_dec(x_73);
x_185 = lean_ctor_get(x_179, 2);
lean_inc(x_185);
x_186 = lean_ctor_get(x_179, 4);
lean_inc(x_186);
lean_dec(x_179);
lean_ctor_set_tag(x_177, 0);
lean_ctor_set(x_177, 0, x_186);
x_187 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_187, 0, x_74);
lean_ctor_set(x_187, 1, x_184);
lean_ctor_set(x_187, 2, x_154);
lean_ctor_set(x_187, 3, x_185);
lean_ctor_set(x_187, 4, x_177);
lean_ctor_set(x_187, 5, x_82);
lean_ctor_set_uint8(x_187, sizeof(void*)*6, x_84);
lean_ctor_set_uint8(x_187, sizeof(void*)*6 + 1, x_76);
x_188 = l_Lean_Compiler_LCNF_Decl_etaExpand(x_187, x_2, x_3, x_4, x_5, x_183);
return x_188;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_177);
x_189 = l_Lean_Compiler_LCNF_eraseFunDecl(x_179, x_84, x_2, x_3, x_4, x_5, x_178);
x_190 = lean_ctor_get(x_189, 1);
lean_inc(x_190);
lean_dec(x_189);
x_191 = l_Lean_ConstantInfo_levelParams(x_73);
lean_dec(x_73);
x_192 = lean_ctor_get(x_179, 2);
lean_inc(x_192);
x_193 = lean_ctor_get(x_179, 4);
lean_inc(x_193);
lean_dec(x_179);
x_194 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_194, 0, x_193);
x_195 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_195, 0, x_74);
lean_ctor_set(x_195, 1, x_191);
lean_ctor_set(x_195, 2, x_154);
lean_ctor_set(x_195, 3, x_192);
lean_ctor_set(x_195, 4, x_194);
lean_ctor_set(x_195, 5, x_82);
lean_ctor_set_uint8(x_195, sizeof(void*)*6, x_84);
lean_ctor_set_uint8(x_195, sizeof(void*)*6 + 1, x_76);
x_196 = l_Lean_Compiler_LCNF_Decl_etaExpand(x_195, x_2, x_3, x_4, x_5, x_190);
return x_196;
}
}
else
{
lean_object* x_197; 
lean_dec(x_177);
x_197 = lean_ctor_get(x_175, 1);
lean_inc(x_197);
lean_dec(x_175);
x_7 = x_76;
x_8 = x_107;
x_9 = x_176;
x_10 = x_73;
x_11 = x_82;
x_12 = x_84;
x_13 = x_74;
x_14 = x_154;
x_15 = x_2;
x_16 = x_3;
x_17 = x_4;
x_18 = x_5;
x_19 = x_197;
goto block_25;
}
}
else
{
lean_object* x_198; 
x_198 = lean_ctor_get(x_175, 1);
lean_inc(x_198);
lean_dec(x_175);
x_7 = x_76;
x_8 = x_107;
x_9 = x_176;
x_10 = x_73;
x_11 = x_82;
x_12 = x_84;
x_13 = x_74;
x_14 = x_154;
x_15 = x_2;
x_16 = x_3;
x_17 = x_4;
x_18 = x_5;
x_19 = x_198;
goto block_25;
}
}
else
{
uint8_t x_199; 
lean_dec(x_154);
lean_dec(x_82);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_199 = !lean_is_exclusive(x_175);
if (x_199 == 0)
{
return x_175;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_175, 0);
x_201 = lean_ctor_get(x_175, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_175);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
else
{
uint8_t x_203; 
lean_dec(x_154);
lean_dec(x_126);
lean_dec(x_82);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_203 = !lean_is_exclusive(x_170);
if (x_203 == 0)
{
return x_170;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_170, 0);
x_205 = lean_ctor_get(x_170, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_170);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
}
else
{
uint8_t x_207; 
lean_dec(x_154);
lean_dec(x_126);
lean_dec(x_82);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_207 = !lean_is_exclusive(x_167);
if (x_207 == 0)
{
return x_167;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_167, 0);
x_209 = lean_ctor_get(x_167, 1);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_167);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
return x_210;
}
}
}
else
{
uint8_t x_211; 
lean_dec(x_154);
lean_dec(x_126);
lean_dec(x_82);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_211 = !lean_is_exclusive(x_164);
if (x_211 == 0)
{
return x_164;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_164, 0);
x_213 = lean_ctor_get(x_164, 1);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_164);
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
return x_214;
}
}
}
else
{
uint8_t x_215; 
lean_dec(x_154);
lean_dec(x_126);
lean_dec(x_82);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_215 = !lean_is_exclusive(x_161);
if (x_215 == 0)
{
return x_161;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_161, 0);
x_217 = lean_ctor_get(x_161, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_161);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
return x_218;
}
}
}
else
{
uint8_t x_219; 
lean_dec(x_154);
lean_dec(x_126);
lean_dec(x_82);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_219 = !lean_is_exclusive(x_158);
if (x_219 == 0)
{
return x_158;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_158, 0);
x_221 = lean_ctor_get(x_158, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_158);
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
return x_222;
}
}
}
else
{
uint8_t x_223; 
lean_dec(x_152);
lean_dec(x_126);
lean_dec(x_96);
lean_dec(x_82);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_223 = !lean_is_exclusive(x_153);
if (x_223 == 0)
{
return x_153;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_224 = lean_ctor_get(x_153, 0);
x_225 = lean_ctor_get(x_153, 1);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_153);
x_226 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_225);
return x_226;
}
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; size_t x_232; lean_object* x_233; lean_object* x_234; size_t x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; uint8_t x_267; uint8_t x_268; uint8_t x_269; uint8_t x_270; uint8_t x_271; uint8_t x_272; uint8_t x_273; uint8_t x_274; uint8_t x_275; uint8_t x_276; uint8_t x_277; uint64_t x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_227 = lean_ctor_get(x_87, 0);
lean_inc(x_227);
lean_dec(x_87);
x_228 = lean_box(0);
x_229 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_230 = lean_unsigned_to_nat(2u);
x_231 = lean_unsigned_to_nat(5u);
x_232 = lean_usize_of_nat(x_231);
x_233 = lean_usize_to_nat(x_232);
x_234 = lean_nat_pow(x_230, x_233);
lean_dec(x_233);
x_235 = lean_usize_of_nat(x_234);
lean_dec(x_234);
x_236 = lean_usize_to_nat(x_235);
x_237 = lean_mk_empty_array_with_capacity(x_236);
lean_dec(x_236);
lean_inc(x_237);
x_238 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_238, 0, x_237);
x_239 = lean_unsigned_to_nat(0u);
lean_inc(x_229);
x_240 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_240, 0, x_229);
lean_inc(x_229);
x_241 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_241, 0, x_229);
lean_inc(x_229);
x_242 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_242, 0, x_229);
lean_inc(x_229);
x_243 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_243, 0, x_229);
lean_inc(x_229);
x_244 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_244, 0, x_229);
lean_inc(x_229);
x_245 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_245, 0, x_229);
lean_inc(x_240);
x_246 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_246, 0, x_239);
lean_ctor_set(x_246, 1, x_239);
lean_ctor_set(x_246, 2, x_239);
lean_ctor_set(x_246, 3, x_240);
lean_ctor_set(x_246, 4, x_241);
lean_ctor_set(x_246, 5, x_242);
lean_ctor_set(x_246, 6, x_243);
lean_ctor_set(x_246, 7, x_244);
lean_ctor_set(x_246, 8, x_245);
lean_inc(x_229);
x_247 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_247, 0, x_229);
lean_inc(x_229);
x_248 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_248, 0, x_229);
lean_inc(x_229);
x_249 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_249, 0, x_229);
lean_inc(x_229);
x_250 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_250, 0, x_229);
lean_inc(x_250);
lean_inc(x_247);
x_251 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_251, 0, x_247);
lean_ctor_set(x_251, 1, x_248);
lean_ctor_set(x_251, 2, x_249);
lean_ctor_set(x_251, 3, x_247);
lean_ctor_set(x_251, 4, x_250);
lean_ctor_set(x_251, 5, x_250);
lean_inc(x_237);
x_252 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_252, 0, x_237);
lean_inc(x_237);
x_253 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_237);
lean_ctor_set(x_253, 2, x_239);
lean_ctor_set(x_253, 3, x_239);
lean_ctor_set_usize(x_253, 4, x_232);
lean_inc(x_229);
x_254 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_254, 0, x_229);
lean_inc_n(x_240, 2);
x_255 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_255, 0, x_240);
lean_ctor_set(x_255, 1, x_240);
lean_ctor_set(x_255, 2, x_240);
lean_ctor_set(x_255, 3, x_254);
x_256 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_256, 0, x_246);
lean_ctor_set(x_256, 1, x_251);
lean_ctor_set(x_256, 2, x_228);
lean_ctor_set(x_256, 3, x_253);
lean_ctor_set(x_256, 4, x_255);
x_257 = lean_st_mk_ref(x_256, x_80);
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
lean_dec(x_257);
x_260 = lean_box(1);
x_261 = lean_box(0);
x_262 = lean_box(2);
x_263 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_263, 0, x_229);
x_264 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_264, 0, x_238);
lean_ctor_set(x_264, 1, x_237);
lean_ctor_set(x_264, 2, x_239);
lean_ctor_set(x_264, 3, x_239);
lean_ctor_set_usize(x_264, 4, x_232);
x_265 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_265, 0, x_84);
lean_ctor_set_uint8(x_265, 1, x_84);
lean_ctor_set_uint8(x_265, 2, x_84);
lean_ctor_set_uint8(x_265, 3, x_84);
lean_ctor_set_uint8(x_265, 4, x_84);
x_266 = lean_unbox(x_85);
lean_ctor_set_uint8(x_265, 5, x_266);
x_267 = lean_unbox(x_85);
lean_ctor_set_uint8(x_265, 6, x_267);
lean_ctor_set_uint8(x_265, 7, x_84);
x_268 = lean_unbox(x_85);
lean_ctor_set_uint8(x_265, 8, x_268);
x_269 = lean_unbox(x_260);
lean_ctor_set_uint8(x_265, 9, x_269);
x_270 = lean_unbox(x_261);
lean_ctor_set_uint8(x_265, 10, x_270);
x_271 = lean_unbox(x_85);
lean_ctor_set_uint8(x_265, 11, x_271);
x_272 = lean_unbox(x_85);
lean_ctor_set_uint8(x_265, 12, x_272);
x_273 = lean_unbox(x_85);
lean_ctor_set_uint8(x_265, 13, x_273);
x_274 = lean_unbox(x_262);
lean_ctor_set_uint8(x_265, 14, x_274);
x_275 = lean_unbox(x_85);
lean_ctor_set_uint8(x_265, 15, x_275);
x_276 = lean_unbox(x_85);
lean_ctor_set_uint8(x_265, 16, x_276);
x_277 = lean_unbox(x_85);
lean_ctor_set_uint8(x_265, 17, x_277);
x_278 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_265);
x_279 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_279, 0, x_263);
lean_ctor_set(x_279, 1, x_264);
lean_ctor_set(x_279, 2, x_228);
x_280 = lean_mk_empty_array_with_capacity(x_239);
x_281 = lean_box(0);
x_282 = lean_box(0);
x_283 = l_Lean_ConstantInfo_type(x_73);
x_284 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_284, 0, x_265);
lean_ctor_set(x_284, 1, x_228);
lean_ctor_set(x_284, 2, x_279);
lean_ctor_set(x_284, 3, x_280);
lean_ctor_set(x_284, 4, x_281);
lean_ctor_set(x_284, 5, x_239);
lean_ctor_set(x_284, 6, x_282);
lean_ctor_set_uint64(x_284, sizeof(void*)*7, x_278);
lean_ctor_set_uint8(x_284, sizeof(void*)*7 + 8, x_84);
lean_ctor_set_uint8(x_284, sizeof(void*)*7 + 9, x_84);
lean_ctor_set_uint8(x_284, sizeof(void*)*7 + 10, x_84);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_258);
lean_inc(x_284);
x_285 = l_Lean_Compiler_LCNF_toLCNFType(x_283, x_284, x_258, x_4, x_5, x_259);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
lean_dec(x_285);
x_288 = lean_box(x_84);
x_289 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_toDecl___lam__1___boxed), 9, 2);
lean_closure_set(x_289, 0, x_288);
lean_closure_set(x_289, 1, x_85);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_258);
x_290 = l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg(x_227, x_289, x_84, x_284, x_258, x_4, x_5, x_287);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_290, 1);
lean_inc(x_292);
lean_dec(x_290);
lean_inc(x_5);
lean_inc(x_4);
x_293 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames(x_291, x_4, x_5, x_292);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_293, 1);
lean_inc(x_295);
lean_dec(x_293);
lean_inc(x_5);
lean_inc(x_4);
x_296 = l_Lean_Compiler_LCNF_macroInline(x_294, x_4, x_5, x_295);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec(x_296);
lean_inc(x_5);
lean_inc(x_4);
x_299 = l_Lean_Compiler_LCNF_inlineMatchers(x_297, x_4, x_5, x_298);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
lean_dec(x_299);
lean_inc(x_5);
lean_inc(x_4);
x_302 = l_Lean_Compiler_LCNF_macroInline(x_300, x_4, x_5, x_301);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_302, 1);
lean_inc(x_304);
lean_dec(x_302);
x_305 = lean_st_ref_get(x_258, x_304);
lean_dec(x_258);
x_306 = lean_ctor_get(x_305, 1);
lean_inc(x_306);
lean_dec(x_305);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_307 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF(x_303, x_2, x_3, x_4, x_5, x_306);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; 
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
if (lean_obj_tag(x_308) == 1)
{
lean_object* x_309; 
x_309 = lean_ctor_get(x_308, 1);
lean_inc(x_309);
if (lean_obj_tag(x_309) == 5)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_310 = lean_ctor_get(x_307, 1);
lean_inc(x_310);
lean_dec(x_307);
x_311 = lean_ctor_get(x_308, 0);
lean_inc(x_311);
lean_dec(x_308);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 x_312 = x_309;
} else {
 lean_dec_ref(x_309);
 x_312 = lean_box(0);
}
x_313 = l_Lean_Compiler_LCNF_eraseFunDecl(x_311, x_84, x_2, x_3, x_4, x_5, x_310);
x_314 = lean_ctor_get(x_313, 1);
lean_inc(x_314);
lean_dec(x_313);
x_315 = l_Lean_ConstantInfo_levelParams(x_73);
lean_dec(x_73);
x_316 = lean_ctor_get(x_311, 2);
lean_inc(x_316);
x_317 = lean_ctor_get(x_311, 4);
lean_inc(x_317);
lean_dec(x_311);
if (lean_is_scalar(x_312)) {
 x_318 = lean_alloc_ctor(0, 1, 0);
} else {
 x_318 = x_312;
 lean_ctor_set_tag(x_318, 0);
}
lean_ctor_set(x_318, 0, x_317);
x_319 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_319, 0, x_74);
lean_ctor_set(x_319, 1, x_315);
lean_ctor_set(x_319, 2, x_286);
lean_ctor_set(x_319, 3, x_316);
lean_ctor_set(x_319, 4, x_318);
lean_ctor_set(x_319, 5, x_82);
lean_ctor_set_uint8(x_319, sizeof(void*)*6, x_84);
lean_ctor_set_uint8(x_319, sizeof(void*)*6 + 1, x_76);
x_320 = l_Lean_Compiler_LCNF_Decl_etaExpand(x_319, x_2, x_3, x_4, x_5, x_314);
return x_320;
}
else
{
lean_object* x_321; 
lean_dec(x_309);
x_321 = lean_ctor_get(x_307, 1);
lean_inc(x_321);
lean_dec(x_307);
x_7 = x_76;
x_8 = x_239;
x_9 = x_308;
x_10 = x_73;
x_11 = x_82;
x_12 = x_84;
x_13 = x_74;
x_14 = x_286;
x_15 = x_2;
x_16 = x_3;
x_17 = x_4;
x_18 = x_5;
x_19 = x_321;
goto block_25;
}
}
else
{
lean_object* x_322; 
x_322 = lean_ctor_get(x_307, 1);
lean_inc(x_322);
lean_dec(x_307);
x_7 = x_76;
x_8 = x_239;
x_9 = x_308;
x_10 = x_73;
x_11 = x_82;
x_12 = x_84;
x_13 = x_74;
x_14 = x_286;
x_15 = x_2;
x_16 = x_3;
x_17 = x_4;
x_18 = x_5;
x_19 = x_322;
goto block_25;
}
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
lean_dec(x_286);
lean_dec(x_82);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_323 = lean_ctor_get(x_307, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_307, 1);
lean_inc(x_324);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 lean_ctor_release(x_307, 1);
 x_325 = x_307;
} else {
 lean_dec_ref(x_307);
 x_325 = lean_box(0);
}
if (lean_is_scalar(x_325)) {
 x_326 = lean_alloc_ctor(1, 2, 0);
} else {
 x_326 = x_325;
}
lean_ctor_set(x_326, 0, x_323);
lean_ctor_set(x_326, 1, x_324);
return x_326;
}
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
lean_dec(x_286);
lean_dec(x_258);
lean_dec(x_82);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_327 = lean_ctor_get(x_302, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_302, 1);
lean_inc(x_328);
if (lean_is_exclusive(x_302)) {
 lean_ctor_release(x_302, 0);
 lean_ctor_release(x_302, 1);
 x_329 = x_302;
} else {
 lean_dec_ref(x_302);
 x_329 = lean_box(0);
}
if (lean_is_scalar(x_329)) {
 x_330 = lean_alloc_ctor(1, 2, 0);
} else {
 x_330 = x_329;
}
lean_ctor_set(x_330, 0, x_327);
lean_ctor_set(x_330, 1, x_328);
return x_330;
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
lean_dec(x_286);
lean_dec(x_258);
lean_dec(x_82);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_331 = lean_ctor_get(x_299, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_299, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 x_333 = x_299;
} else {
 lean_dec_ref(x_299);
 x_333 = lean_box(0);
}
if (lean_is_scalar(x_333)) {
 x_334 = lean_alloc_ctor(1, 2, 0);
} else {
 x_334 = x_333;
}
lean_ctor_set(x_334, 0, x_331);
lean_ctor_set(x_334, 1, x_332);
return x_334;
}
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
lean_dec(x_286);
lean_dec(x_258);
lean_dec(x_82);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_335 = lean_ctor_get(x_296, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_296, 1);
lean_inc(x_336);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 lean_ctor_release(x_296, 1);
 x_337 = x_296;
} else {
 lean_dec_ref(x_296);
 x_337 = lean_box(0);
}
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(1, 2, 0);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_335);
lean_ctor_set(x_338, 1, x_336);
return x_338;
}
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
lean_dec(x_286);
lean_dec(x_258);
lean_dec(x_82);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_339 = lean_ctor_get(x_293, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_293, 1);
lean_inc(x_340);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 x_341 = x_293;
} else {
 lean_dec_ref(x_293);
 x_341 = lean_box(0);
}
if (lean_is_scalar(x_341)) {
 x_342 = lean_alloc_ctor(1, 2, 0);
} else {
 x_342 = x_341;
}
lean_ctor_set(x_342, 0, x_339);
lean_ctor_set(x_342, 1, x_340);
return x_342;
}
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
lean_dec(x_286);
lean_dec(x_258);
lean_dec(x_82);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_343 = lean_ctor_get(x_290, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_290, 1);
lean_inc(x_344);
if (lean_is_exclusive(x_290)) {
 lean_ctor_release(x_290, 0);
 lean_ctor_release(x_290, 1);
 x_345 = x_290;
} else {
 lean_dec_ref(x_290);
 x_345 = lean_box(0);
}
if (lean_is_scalar(x_345)) {
 x_346 = lean_alloc_ctor(1, 2, 0);
} else {
 x_346 = x_345;
}
lean_ctor_set(x_346, 0, x_343);
lean_ctor_set(x_346, 1, x_344);
return x_346;
}
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
lean_dec(x_284);
lean_dec(x_258);
lean_dec(x_227);
lean_dec(x_82);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_347 = lean_ctor_get(x_285, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_285, 1);
lean_inc(x_348);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_349 = x_285;
} else {
 lean_dec_ref(x_285);
 x_349 = lean_box(0);
}
if (lean_is_scalar(x_349)) {
 x_350 = lean_alloc_ctor(1, 2, 0);
} else {
 x_350 = x_349;
}
lean_ctor_set(x_350, 0, x_347);
lean_ctor_set(x_350, 1, x_348);
return x_350;
}
}
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; size_t x_355; lean_object* x_356; lean_object* x_357; size_t x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; uint8_t x_390; uint8_t x_391; uint8_t x_392; uint8_t x_393; uint8_t x_394; uint8_t x_395; uint8_t x_396; uint8_t x_397; uint8_t x_398; uint8_t x_399; uint8_t x_400; uint8_t x_401; uint8_t x_402; uint8_t x_403; uint8_t x_404; uint8_t x_405; uint8_t x_406; uint8_t x_407; uint64_t x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; uint8_t x_416; uint8_t x_417; lean_object* x_418; 
lean_free_object(x_77);
x_351 = lean_box(0);
x_352 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_353 = lean_unsigned_to_nat(2u);
x_354 = lean_unsigned_to_nat(5u);
x_355 = lean_usize_of_nat(x_354);
x_356 = lean_usize_to_nat(x_355);
x_357 = lean_nat_pow(x_353, x_356);
lean_dec(x_356);
x_358 = lean_usize_of_nat(x_357);
lean_dec(x_357);
x_359 = lean_usize_to_nat(x_358);
x_360 = lean_mk_empty_array_with_capacity(x_359);
lean_dec(x_359);
lean_inc(x_360);
x_361 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_361, 0, x_360);
x_362 = lean_unsigned_to_nat(0u);
lean_inc(x_352);
x_363 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_363, 0, x_352);
lean_inc(x_352);
x_364 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_364, 0, x_352);
lean_inc(x_352);
x_365 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_365, 0, x_352);
lean_inc(x_352);
x_366 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_366, 0, x_352);
lean_inc(x_352);
x_367 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_367, 0, x_352);
lean_inc(x_352);
x_368 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_368, 0, x_352);
lean_inc(x_363);
x_369 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_369, 0, x_362);
lean_ctor_set(x_369, 1, x_362);
lean_ctor_set(x_369, 2, x_362);
lean_ctor_set(x_369, 3, x_363);
lean_ctor_set(x_369, 4, x_364);
lean_ctor_set(x_369, 5, x_365);
lean_ctor_set(x_369, 6, x_366);
lean_ctor_set(x_369, 7, x_367);
lean_ctor_set(x_369, 8, x_368);
lean_inc(x_352);
x_370 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_370, 0, x_352);
lean_inc(x_352);
x_371 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_371, 0, x_352);
lean_inc(x_352);
x_372 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_372, 0, x_352);
lean_inc(x_352);
x_373 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_373, 0, x_352);
lean_inc(x_373);
lean_inc(x_370);
x_374 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_374, 0, x_370);
lean_ctor_set(x_374, 1, x_371);
lean_ctor_set(x_374, 2, x_372);
lean_ctor_set(x_374, 3, x_370);
lean_ctor_set(x_374, 4, x_373);
lean_ctor_set(x_374, 5, x_373);
lean_inc(x_360);
x_375 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_375, 0, x_360);
lean_inc(x_360);
x_376 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_360);
lean_ctor_set(x_376, 2, x_362);
lean_ctor_set(x_376, 3, x_362);
lean_ctor_set_usize(x_376, 4, x_355);
lean_inc(x_352);
x_377 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_377, 0, x_352);
lean_inc_n(x_363, 2);
x_378 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_378, 0, x_363);
lean_ctor_set(x_378, 1, x_363);
lean_ctor_set(x_378, 2, x_363);
lean_ctor_set(x_378, 3, x_377);
x_379 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_379, 0, x_369);
lean_ctor_set(x_379, 1, x_374);
lean_ctor_set(x_379, 2, x_351);
lean_ctor_set(x_379, 3, x_376);
lean_ctor_set(x_379, 4, x_378);
x_380 = lean_st_mk_ref(x_379, x_80);
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_380, 1);
lean_inc(x_382);
lean_dec(x_380);
x_383 = lean_box(1);
x_384 = lean_box(0);
x_385 = lean_box(2);
x_386 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_386, 0, x_352);
x_387 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_387, 0, x_361);
lean_ctor_set(x_387, 1, x_360);
lean_ctor_set(x_387, 2, x_362);
lean_ctor_set(x_387, 3, x_362);
lean_ctor_set_usize(x_387, 4, x_355);
x_388 = lean_box(0);
x_389 = lean_alloc_ctor(0, 0, 18);
x_390 = lean_unbox(x_388);
lean_ctor_set_uint8(x_389, 0, x_390);
x_391 = lean_unbox(x_388);
lean_ctor_set_uint8(x_389, 1, x_391);
x_392 = lean_unbox(x_388);
lean_ctor_set_uint8(x_389, 2, x_392);
x_393 = lean_unbox(x_388);
lean_ctor_set_uint8(x_389, 3, x_393);
x_394 = lean_unbox(x_388);
lean_ctor_set_uint8(x_389, 4, x_394);
x_395 = lean_unbox(x_85);
lean_ctor_set_uint8(x_389, 5, x_395);
x_396 = lean_unbox(x_85);
lean_ctor_set_uint8(x_389, 6, x_396);
x_397 = lean_unbox(x_388);
lean_ctor_set_uint8(x_389, 7, x_397);
x_398 = lean_unbox(x_85);
lean_ctor_set_uint8(x_389, 8, x_398);
x_399 = lean_unbox(x_383);
lean_ctor_set_uint8(x_389, 9, x_399);
x_400 = lean_unbox(x_384);
lean_ctor_set_uint8(x_389, 10, x_400);
x_401 = lean_unbox(x_85);
lean_ctor_set_uint8(x_389, 11, x_401);
x_402 = lean_unbox(x_85);
lean_ctor_set_uint8(x_389, 12, x_402);
x_403 = lean_unbox(x_85);
lean_ctor_set_uint8(x_389, 13, x_403);
x_404 = lean_unbox(x_385);
lean_ctor_set_uint8(x_389, 14, x_404);
x_405 = lean_unbox(x_85);
lean_ctor_set_uint8(x_389, 15, x_405);
x_406 = lean_unbox(x_85);
lean_ctor_set_uint8(x_389, 16, x_406);
x_407 = lean_unbox(x_85);
lean_ctor_set_uint8(x_389, 17, x_407);
x_408 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_389);
x_409 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_409, 0, x_386);
lean_ctor_set(x_409, 1, x_387);
lean_ctor_set(x_409, 2, x_351);
x_410 = lean_mk_empty_array_with_capacity(x_362);
x_411 = lean_box(0);
x_412 = lean_box(0);
x_413 = l_Lean_ConstantInfo_type(x_73);
x_414 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_414, 0, x_389);
lean_ctor_set(x_414, 1, x_351);
lean_ctor_set(x_414, 2, x_409);
lean_ctor_set(x_414, 3, x_410);
lean_ctor_set(x_414, 4, x_411);
lean_ctor_set(x_414, 5, x_362);
lean_ctor_set(x_414, 6, x_412);
lean_ctor_set_uint64(x_414, sizeof(void*)*7, x_408);
x_415 = lean_unbox(x_388);
lean_ctor_set_uint8(x_414, sizeof(void*)*7 + 8, x_415);
x_416 = lean_unbox(x_388);
lean_ctor_set_uint8(x_414, sizeof(void*)*7 + 9, x_416);
x_417 = lean_unbox(x_388);
lean_ctor_set_uint8(x_414, sizeof(void*)*7 + 10, x_417);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_381);
x_418 = l_Lean_Compiler_LCNF_toLCNFType(x_413, x_414, x_381, x_4, x_5, x_382);
if (lean_obj_tag(x_418) == 0)
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; uint8_t x_423; 
x_419 = lean_ctor_get(x_418, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_418, 1);
lean_inc(x_420);
lean_dec(x_418);
x_421 = lean_st_ref_get(x_381, x_420);
lean_dec(x_381);
x_422 = lean_ctor_get(x_421, 1);
lean_inc(x_422);
lean_dec(x_421);
x_423 = lean_unbox(x_388);
x_47 = x_76;
x_48 = x_423;
x_49 = x_73;
x_50 = x_82;
x_51 = x_74;
x_52 = x_419;
x_53 = x_422;
goto block_72;
}
else
{
lean_dec(x_381);
if (lean_obj_tag(x_418) == 0)
{
lean_object* x_424; lean_object* x_425; uint8_t x_426; 
x_424 = lean_ctor_get(x_418, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_418, 1);
lean_inc(x_425);
lean_dec(x_418);
x_426 = lean_unbox(x_388);
x_47 = x_76;
x_48 = x_426;
x_49 = x_73;
x_50 = x_82;
x_51 = x_74;
x_52 = x_424;
x_53 = x_425;
goto block_72;
}
else
{
uint8_t x_427; 
lean_dec(x_82);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_427 = !lean_is_exclusive(x_418);
if (x_427 == 0)
{
return x_418;
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_428 = lean_ctor_get(x_418, 0);
x_429 = lean_ctor_get(x_418, 1);
lean_inc(x_429);
lean_inc(x_428);
lean_dec(x_418);
x_430 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_430, 0, x_428);
lean_ctor_set(x_430, 1, x_429);
return x_430;
}
}
}
}
}
else
{
uint8_t x_431; 
lean_dec(x_81);
lean_free_object(x_77);
x_431 = !lean_is_exclusive(x_83);
if (x_431 == 0)
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; size_t x_437; lean_object* x_438; lean_object* x_439; size_t x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; uint8_t x_472; uint8_t x_473; uint8_t x_474; uint8_t x_475; uint8_t x_476; uint8_t x_477; uint8_t x_478; uint8_t x_479; uint8_t x_480; uint8_t x_481; uint8_t x_482; uint8_t x_483; uint8_t x_484; uint8_t x_485; uint8_t x_486; uint8_t x_487; uint8_t x_488; uint8_t x_489; uint64_t x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; uint8_t x_497; uint8_t x_498; uint8_t x_499; lean_object* x_500; 
x_432 = lean_ctor_get(x_83, 0);
x_433 = lean_box(0);
x_434 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_435 = lean_unsigned_to_nat(2u);
x_436 = lean_unsigned_to_nat(5u);
x_437 = lean_usize_of_nat(x_436);
x_438 = lean_usize_to_nat(x_437);
x_439 = lean_nat_pow(x_435, x_438);
lean_dec(x_438);
x_440 = lean_usize_of_nat(x_439);
lean_dec(x_439);
x_441 = lean_usize_to_nat(x_440);
x_442 = lean_mk_empty_array_with_capacity(x_441);
lean_dec(x_441);
lean_inc(x_442);
lean_ctor_set_tag(x_83, 0);
lean_ctor_set(x_83, 0, x_442);
x_443 = lean_unsigned_to_nat(0u);
lean_inc(x_434);
x_444 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_444, 0, x_434);
lean_inc(x_434);
x_445 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_445, 0, x_434);
lean_inc(x_434);
x_446 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_446, 0, x_434);
lean_inc(x_434);
x_447 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_447, 0, x_434);
lean_inc(x_434);
x_448 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_448, 0, x_434);
lean_inc(x_434);
x_449 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_449, 0, x_434);
lean_inc(x_444);
x_450 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_450, 0, x_443);
lean_ctor_set(x_450, 1, x_443);
lean_ctor_set(x_450, 2, x_443);
lean_ctor_set(x_450, 3, x_444);
lean_ctor_set(x_450, 4, x_445);
lean_ctor_set(x_450, 5, x_446);
lean_ctor_set(x_450, 6, x_447);
lean_ctor_set(x_450, 7, x_448);
lean_ctor_set(x_450, 8, x_449);
lean_inc(x_434);
x_451 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_451, 0, x_434);
lean_inc(x_434);
x_452 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_452, 0, x_434);
lean_inc(x_434);
x_453 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_453, 0, x_434);
lean_inc(x_434);
x_454 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_454, 0, x_434);
lean_inc(x_454);
lean_inc(x_451);
x_455 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_455, 0, x_451);
lean_ctor_set(x_455, 1, x_452);
lean_ctor_set(x_455, 2, x_453);
lean_ctor_set(x_455, 3, x_451);
lean_ctor_set(x_455, 4, x_454);
lean_ctor_set(x_455, 5, x_454);
lean_inc(x_442);
x_456 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_456, 0, x_442);
lean_inc(x_442);
x_457 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_457, 0, x_456);
lean_ctor_set(x_457, 1, x_442);
lean_ctor_set(x_457, 2, x_443);
lean_ctor_set(x_457, 3, x_443);
lean_ctor_set_usize(x_457, 4, x_437);
lean_inc(x_434);
x_458 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_458, 0, x_434);
lean_inc_n(x_444, 2);
x_459 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_459, 0, x_444);
lean_ctor_set(x_459, 1, x_444);
lean_ctor_set(x_459, 2, x_444);
lean_ctor_set(x_459, 3, x_458);
x_460 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_460, 0, x_450);
lean_ctor_set(x_460, 1, x_455);
lean_ctor_set(x_460, 2, x_433);
lean_ctor_set(x_460, 3, x_457);
lean_ctor_set(x_460, 4, x_459);
x_461 = lean_st_mk_ref(x_460, x_80);
x_462 = lean_ctor_get(x_461, 0);
lean_inc(x_462);
x_463 = lean_ctor_get(x_461, 1);
lean_inc(x_463);
lean_dec(x_461);
x_464 = lean_box(1);
x_465 = lean_box(1);
x_466 = lean_box(0);
x_467 = lean_box(2);
x_468 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_468, 0, x_434);
x_469 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_469, 0, x_83);
lean_ctor_set(x_469, 1, x_442);
lean_ctor_set(x_469, 2, x_443);
lean_ctor_set(x_469, 3, x_443);
lean_ctor_set_usize(x_469, 4, x_437);
x_470 = lean_box(0);
x_471 = lean_alloc_ctor(0, 0, 18);
x_472 = lean_unbox(x_470);
lean_ctor_set_uint8(x_471, 0, x_472);
x_473 = lean_unbox(x_470);
lean_ctor_set_uint8(x_471, 1, x_473);
x_474 = lean_unbox(x_470);
lean_ctor_set_uint8(x_471, 2, x_474);
x_475 = lean_unbox(x_470);
lean_ctor_set_uint8(x_471, 3, x_475);
x_476 = lean_unbox(x_470);
lean_ctor_set_uint8(x_471, 4, x_476);
x_477 = lean_unbox(x_464);
lean_ctor_set_uint8(x_471, 5, x_477);
x_478 = lean_unbox(x_464);
lean_ctor_set_uint8(x_471, 6, x_478);
x_479 = lean_unbox(x_470);
lean_ctor_set_uint8(x_471, 7, x_479);
x_480 = lean_unbox(x_464);
lean_ctor_set_uint8(x_471, 8, x_480);
x_481 = lean_unbox(x_465);
lean_ctor_set_uint8(x_471, 9, x_481);
x_482 = lean_unbox(x_466);
lean_ctor_set_uint8(x_471, 10, x_482);
x_483 = lean_unbox(x_464);
lean_ctor_set_uint8(x_471, 11, x_483);
x_484 = lean_unbox(x_464);
lean_ctor_set_uint8(x_471, 12, x_484);
x_485 = lean_unbox(x_464);
lean_ctor_set_uint8(x_471, 13, x_485);
x_486 = lean_unbox(x_467);
lean_ctor_set_uint8(x_471, 14, x_486);
x_487 = lean_unbox(x_464);
lean_ctor_set_uint8(x_471, 15, x_487);
x_488 = lean_unbox(x_464);
lean_ctor_set_uint8(x_471, 16, x_488);
x_489 = lean_unbox(x_464);
lean_ctor_set_uint8(x_471, 17, x_489);
x_490 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_471);
x_491 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_491, 0, x_468);
lean_ctor_set(x_491, 1, x_469);
lean_ctor_set(x_491, 2, x_433);
x_492 = lean_mk_empty_array_with_capacity(x_443);
x_493 = lean_box(0);
x_494 = lean_box(0);
x_495 = l_Lean_ConstantInfo_type(x_73);
x_496 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_496, 0, x_471);
lean_ctor_set(x_496, 1, x_433);
lean_ctor_set(x_496, 2, x_491);
lean_ctor_set(x_496, 3, x_492);
lean_ctor_set(x_496, 4, x_493);
lean_ctor_set(x_496, 5, x_443);
lean_ctor_set(x_496, 6, x_494);
lean_ctor_set_uint64(x_496, sizeof(void*)*7, x_490);
x_497 = lean_unbox(x_470);
lean_ctor_set_uint8(x_496, sizeof(void*)*7 + 8, x_497);
x_498 = lean_unbox(x_470);
lean_ctor_set_uint8(x_496, sizeof(void*)*7 + 9, x_498);
x_499 = lean_unbox(x_470);
lean_ctor_set_uint8(x_496, sizeof(void*)*7 + 10, x_499);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_462);
x_500 = l_Lean_Compiler_LCNF_toLCNFType(x_495, x_496, x_462, x_4, x_5, x_463);
if (lean_obj_tag(x_500) == 0)
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; uint8_t x_505; 
x_501 = lean_ctor_get(x_500, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_500, 1);
lean_inc(x_502);
lean_dec(x_500);
x_503 = lean_st_ref_get(x_462, x_502);
lean_dec(x_462);
x_504 = lean_ctor_get(x_503, 1);
lean_inc(x_504);
lean_dec(x_503);
x_505 = lean_unbox(x_470);
x_26 = x_76;
x_27 = x_432;
x_28 = x_73;
x_29 = x_82;
x_30 = x_74;
x_31 = x_505;
x_32 = x_501;
x_33 = x_504;
goto block_46;
}
else
{
lean_dec(x_462);
if (lean_obj_tag(x_500) == 0)
{
lean_object* x_506; lean_object* x_507; uint8_t x_508; 
x_506 = lean_ctor_get(x_500, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_500, 1);
lean_inc(x_507);
lean_dec(x_500);
x_508 = lean_unbox(x_470);
x_26 = x_76;
x_27 = x_432;
x_28 = x_73;
x_29 = x_82;
x_30 = x_74;
x_31 = x_508;
x_32 = x_506;
x_33 = x_507;
goto block_46;
}
else
{
uint8_t x_509; 
lean_dec(x_432);
lean_dec(x_82);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_509 = !lean_is_exclusive(x_500);
if (x_509 == 0)
{
return x_500;
}
else
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; 
x_510 = lean_ctor_get(x_500, 0);
x_511 = lean_ctor_get(x_500, 1);
lean_inc(x_511);
lean_inc(x_510);
lean_dec(x_500);
x_512 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_512, 0, x_510);
lean_ctor_set(x_512, 1, x_511);
return x_512;
}
}
}
}
else
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; size_t x_518; lean_object* x_519; lean_object* x_520; size_t x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; uint8_t x_554; uint8_t x_555; uint8_t x_556; uint8_t x_557; uint8_t x_558; uint8_t x_559; uint8_t x_560; uint8_t x_561; uint8_t x_562; uint8_t x_563; uint8_t x_564; uint8_t x_565; uint8_t x_566; uint8_t x_567; uint8_t x_568; uint8_t x_569; uint8_t x_570; uint8_t x_571; uint64_t x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; uint8_t x_579; uint8_t x_580; uint8_t x_581; lean_object* x_582; 
x_513 = lean_ctor_get(x_83, 0);
lean_inc(x_513);
lean_dec(x_83);
x_514 = lean_box(0);
x_515 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_516 = lean_unsigned_to_nat(2u);
x_517 = lean_unsigned_to_nat(5u);
x_518 = lean_usize_of_nat(x_517);
x_519 = lean_usize_to_nat(x_518);
x_520 = lean_nat_pow(x_516, x_519);
lean_dec(x_519);
x_521 = lean_usize_of_nat(x_520);
lean_dec(x_520);
x_522 = lean_usize_to_nat(x_521);
x_523 = lean_mk_empty_array_with_capacity(x_522);
lean_dec(x_522);
lean_inc(x_523);
x_524 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_524, 0, x_523);
x_525 = lean_unsigned_to_nat(0u);
lean_inc(x_515);
x_526 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_526, 0, x_515);
lean_inc(x_515);
x_527 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_527, 0, x_515);
lean_inc(x_515);
x_528 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_528, 0, x_515);
lean_inc(x_515);
x_529 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_529, 0, x_515);
lean_inc(x_515);
x_530 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_530, 0, x_515);
lean_inc(x_515);
x_531 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_531, 0, x_515);
lean_inc(x_526);
x_532 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_532, 0, x_525);
lean_ctor_set(x_532, 1, x_525);
lean_ctor_set(x_532, 2, x_525);
lean_ctor_set(x_532, 3, x_526);
lean_ctor_set(x_532, 4, x_527);
lean_ctor_set(x_532, 5, x_528);
lean_ctor_set(x_532, 6, x_529);
lean_ctor_set(x_532, 7, x_530);
lean_ctor_set(x_532, 8, x_531);
lean_inc(x_515);
x_533 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_533, 0, x_515);
lean_inc(x_515);
x_534 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_534, 0, x_515);
lean_inc(x_515);
x_535 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_535, 0, x_515);
lean_inc(x_515);
x_536 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_536, 0, x_515);
lean_inc(x_536);
lean_inc(x_533);
x_537 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_537, 0, x_533);
lean_ctor_set(x_537, 1, x_534);
lean_ctor_set(x_537, 2, x_535);
lean_ctor_set(x_537, 3, x_533);
lean_ctor_set(x_537, 4, x_536);
lean_ctor_set(x_537, 5, x_536);
lean_inc(x_523);
x_538 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_538, 0, x_523);
lean_inc(x_523);
x_539 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_539, 0, x_538);
lean_ctor_set(x_539, 1, x_523);
lean_ctor_set(x_539, 2, x_525);
lean_ctor_set(x_539, 3, x_525);
lean_ctor_set_usize(x_539, 4, x_518);
lean_inc(x_515);
x_540 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_540, 0, x_515);
lean_inc_n(x_526, 2);
x_541 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_541, 0, x_526);
lean_ctor_set(x_541, 1, x_526);
lean_ctor_set(x_541, 2, x_526);
lean_ctor_set(x_541, 3, x_540);
x_542 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_542, 0, x_532);
lean_ctor_set(x_542, 1, x_537);
lean_ctor_set(x_542, 2, x_514);
lean_ctor_set(x_542, 3, x_539);
lean_ctor_set(x_542, 4, x_541);
x_543 = lean_st_mk_ref(x_542, x_80);
x_544 = lean_ctor_get(x_543, 0);
lean_inc(x_544);
x_545 = lean_ctor_get(x_543, 1);
lean_inc(x_545);
lean_dec(x_543);
x_546 = lean_box(1);
x_547 = lean_box(1);
x_548 = lean_box(0);
x_549 = lean_box(2);
x_550 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_550, 0, x_515);
x_551 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_551, 0, x_524);
lean_ctor_set(x_551, 1, x_523);
lean_ctor_set(x_551, 2, x_525);
lean_ctor_set(x_551, 3, x_525);
lean_ctor_set_usize(x_551, 4, x_518);
x_552 = lean_box(0);
x_553 = lean_alloc_ctor(0, 0, 18);
x_554 = lean_unbox(x_552);
lean_ctor_set_uint8(x_553, 0, x_554);
x_555 = lean_unbox(x_552);
lean_ctor_set_uint8(x_553, 1, x_555);
x_556 = lean_unbox(x_552);
lean_ctor_set_uint8(x_553, 2, x_556);
x_557 = lean_unbox(x_552);
lean_ctor_set_uint8(x_553, 3, x_557);
x_558 = lean_unbox(x_552);
lean_ctor_set_uint8(x_553, 4, x_558);
x_559 = lean_unbox(x_546);
lean_ctor_set_uint8(x_553, 5, x_559);
x_560 = lean_unbox(x_546);
lean_ctor_set_uint8(x_553, 6, x_560);
x_561 = lean_unbox(x_552);
lean_ctor_set_uint8(x_553, 7, x_561);
x_562 = lean_unbox(x_546);
lean_ctor_set_uint8(x_553, 8, x_562);
x_563 = lean_unbox(x_547);
lean_ctor_set_uint8(x_553, 9, x_563);
x_564 = lean_unbox(x_548);
lean_ctor_set_uint8(x_553, 10, x_564);
x_565 = lean_unbox(x_546);
lean_ctor_set_uint8(x_553, 11, x_565);
x_566 = lean_unbox(x_546);
lean_ctor_set_uint8(x_553, 12, x_566);
x_567 = lean_unbox(x_546);
lean_ctor_set_uint8(x_553, 13, x_567);
x_568 = lean_unbox(x_549);
lean_ctor_set_uint8(x_553, 14, x_568);
x_569 = lean_unbox(x_546);
lean_ctor_set_uint8(x_553, 15, x_569);
x_570 = lean_unbox(x_546);
lean_ctor_set_uint8(x_553, 16, x_570);
x_571 = lean_unbox(x_546);
lean_ctor_set_uint8(x_553, 17, x_571);
x_572 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_553);
x_573 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_573, 0, x_550);
lean_ctor_set(x_573, 1, x_551);
lean_ctor_set(x_573, 2, x_514);
x_574 = lean_mk_empty_array_with_capacity(x_525);
x_575 = lean_box(0);
x_576 = lean_box(0);
x_577 = l_Lean_ConstantInfo_type(x_73);
x_578 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_578, 0, x_553);
lean_ctor_set(x_578, 1, x_514);
lean_ctor_set(x_578, 2, x_573);
lean_ctor_set(x_578, 3, x_574);
lean_ctor_set(x_578, 4, x_575);
lean_ctor_set(x_578, 5, x_525);
lean_ctor_set(x_578, 6, x_576);
lean_ctor_set_uint64(x_578, sizeof(void*)*7, x_572);
x_579 = lean_unbox(x_552);
lean_ctor_set_uint8(x_578, sizeof(void*)*7 + 8, x_579);
x_580 = lean_unbox(x_552);
lean_ctor_set_uint8(x_578, sizeof(void*)*7 + 9, x_580);
x_581 = lean_unbox(x_552);
lean_ctor_set_uint8(x_578, sizeof(void*)*7 + 10, x_581);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_544);
x_582 = l_Lean_Compiler_LCNF_toLCNFType(x_577, x_578, x_544, x_4, x_5, x_545);
if (lean_obj_tag(x_582) == 0)
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; uint8_t x_587; 
x_583 = lean_ctor_get(x_582, 0);
lean_inc(x_583);
x_584 = lean_ctor_get(x_582, 1);
lean_inc(x_584);
lean_dec(x_582);
x_585 = lean_st_ref_get(x_544, x_584);
lean_dec(x_544);
x_586 = lean_ctor_get(x_585, 1);
lean_inc(x_586);
lean_dec(x_585);
x_587 = lean_unbox(x_552);
x_26 = x_76;
x_27 = x_513;
x_28 = x_73;
x_29 = x_82;
x_30 = x_74;
x_31 = x_587;
x_32 = x_583;
x_33 = x_586;
goto block_46;
}
else
{
lean_dec(x_544);
if (lean_obj_tag(x_582) == 0)
{
lean_object* x_588; lean_object* x_589; uint8_t x_590; 
x_588 = lean_ctor_get(x_582, 0);
lean_inc(x_588);
x_589 = lean_ctor_get(x_582, 1);
lean_inc(x_589);
lean_dec(x_582);
x_590 = lean_unbox(x_552);
x_26 = x_76;
x_27 = x_513;
x_28 = x_73;
x_29 = x_82;
x_30 = x_74;
x_31 = x_590;
x_32 = x_588;
x_33 = x_589;
goto block_46;
}
else
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; 
lean_dec(x_513);
lean_dec(x_82);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_591 = lean_ctor_get(x_582, 0);
lean_inc(x_591);
x_592 = lean_ctor_get(x_582, 1);
lean_inc(x_592);
if (lean_is_exclusive(x_582)) {
 lean_ctor_release(x_582, 0);
 lean_ctor_release(x_582, 1);
 x_593 = x_582;
} else {
 lean_dec_ref(x_582);
 x_593 = lean_box(0);
}
if (lean_is_scalar(x_593)) {
 x_594 = lean_alloc_ctor(1, 2, 0);
} else {
 x_594 = x_593;
}
lean_ctor_set(x_594, 0, x_591);
lean_ctor_set(x_594, 1, x_592);
return x_594;
}
}
}
}
}
else
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; 
x_595 = lean_ctor_get(x_77, 0);
x_596 = lean_ctor_get(x_77, 1);
lean_inc(x_596);
lean_inc(x_595);
lean_dec(x_77);
x_597 = lean_ctor_get(x_595, 0);
lean_inc(x_597);
lean_dec(x_595);
lean_inc(x_74);
lean_inc(x_597);
x_598 = l_Lean_Compiler_getInlineAttribute_x3f(x_597, x_74);
lean_inc(x_74);
lean_inc(x_597);
x_599 = lean_get_extern_attr_data(x_597, x_74);
if (lean_obj_tag(x_599) == 0)
{
uint8_t x_600; lean_object* x_601; 
lean_inc(x_74);
x_600 = l_Lean_hasInitAttr(x_597, x_74);
x_601 = lean_box(1);
if (x_600 == 0)
{
uint8_t x_602; lean_object* x_603; 
x_602 = lean_unbox(x_601);
lean_inc(x_73);
x_603 = l_Lean_ConstantInfo_value_x3f(x_73, x_602);
if (lean_obj_tag(x_603) == 0)
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; 
lean_dec(x_598);
lean_dec(x_73);
x_604 = lean_mk_string_unchecked("declaration `", 13, 13);
x_605 = l_Lean_stringToMessageData(x_604);
lean_dec(x_604);
x_606 = l_Lean_MessageData_ofName(x_74);
x_607 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_607, 0, x_605);
lean_ctor_set(x_607, 1, x_606);
x_608 = lean_mk_string_unchecked("` does not have a value", 23, 23);
x_609 = l_Lean_stringToMessageData(x_608);
lean_dec(x_608);
x_610 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_610, 0, x_607);
lean_ctor_set(x_610, 1, x_609);
x_611 = l_Lean_throwError___at___Lean_Compiler_LCNF_getType_spec__1(lean_box(0), x_610, x_2, x_3, x_4, x_5, x_596);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_611;
}
else
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; size_t x_618; lean_object* x_619; lean_object* x_620; size_t x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; uint8_t x_652; uint8_t x_653; uint8_t x_654; uint8_t x_655; uint8_t x_656; uint8_t x_657; uint8_t x_658; uint8_t x_659; uint8_t x_660; uint8_t x_661; uint8_t x_662; uint8_t x_663; uint64_t x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; 
x_612 = lean_ctor_get(x_603, 0);
lean_inc(x_612);
if (lean_is_exclusive(x_603)) {
 lean_ctor_release(x_603, 0);
 x_613 = x_603;
} else {
 lean_dec_ref(x_603);
 x_613 = lean_box(0);
}
x_614 = lean_box(0);
x_615 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_616 = lean_unsigned_to_nat(2u);
x_617 = lean_unsigned_to_nat(5u);
x_618 = lean_usize_of_nat(x_617);
x_619 = lean_usize_to_nat(x_618);
x_620 = lean_nat_pow(x_616, x_619);
lean_dec(x_619);
x_621 = lean_usize_of_nat(x_620);
lean_dec(x_620);
x_622 = lean_usize_to_nat(x_621);
x_623 = lean_mk_empty_array_with_capacity(x_622);
lean_dec(x_622);
lean_inc(x_623);
if (lean_is_scalar(x_613)) {
 x_624 = lean_alloc_ctor(0, 1, 0);
} else {
 x_624 = x_613;
 lean_ctor_set_tag(x_624, 0);
}
lean_ctor_set(x_624, 0, x_623);
x_625 = lean_unsigned_to_nat(0u);
lean_inc(x_615);
x_626 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_626, 0, x_615);
lean_inc(x_615);
x_627 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_627, 0, x_615);
lean_inc(x_615);
x_628 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_628, 0, x_615);
lean_inc(x_615);
x_629 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_629, 0, x_615);
lean_inc(x_615);
x_630 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_630, 0, x_615);
lean_inc(x_615);
x_631 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_631, 0, x_615);
lean_inc(x_626);
x_632 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_632, 0, x_625);
lean_ctor_set(x_632, 1, x_625);
lean_ctor_set(x_632, 2, x_625);
lean_ctor_set(x_632, 3, x_626);
lean_ctor_set(x_632, 4, x_627);
lean_ctor_set(x_632, 5, x_628);
lean_ctor_set(x_632, 6, x_629);
lean_ctor_set(x_632, 7, x_630);
lean_ctor_set(x_632, 8, x_631);
lean_inc(x_615);
x_633 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_633, 0, x_615);
lean_inc(x_615);
x_634 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_634, 0, x_615);
lean_inc(x_615);
x_635 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_635, 0, x_615);
lean_inc(x_615);
x_636 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_636, 0, x_615);
lean_inc(x_636);
lean_inc(x_633);
x_637 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_637, 0, x_633);
lean_ctor_set(x_637, 1, x_634);
lean_ctor_set(x_637, 2, x_635);
lean_ctor_set(x_637, 3, x_633);
lean_ctor_set(x_637, 4, x_636);
lean_ctor_set(x_637, 5, x_636);
lean_inc(x_623);
x_638 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_638, 0, x_623);
lean_inc(x_623);
x_639 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_639, 0, x_638);
lean_ctor_set(x_639, 1, x_623);
lean_ctor_set(x_639, 2, x_625);
lean_ctor_set(x_639, 3, x_625);
lean_ctor_set_usize(x_639, 4, x_618);
lean_inc(x_615);
x_640 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_640, 0, x_615);
lean_inc_n(x_626, 2);
x_641 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_641, 0, x_626);
lean_ctor_set(x_641, 1, x_626);
lean_ctor_set(x_641, 2, x_626);
lean_ctor_set(x_641, 3, x_640);
x_642 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_642, 0, x_632);
lean_ctor_set(x_642, 1, x_637);
lean_ctor_set(x_642, 2, x_614);
lean_ctor_set(x_642, 3, x_639);
lean_ctor_set(x_642, 4, x_641);
x_643 = lean_st_mk_ref(x_642, x_596);
x_644 = lean_ctor_get(x_643, 0);
lean_inc(x_644);
x_645 = lean_ctor_get(x_643, 1);
lean_inc(x_645);
lean_dec(x_643);
x_646 = lean_box(1);
x_647 = lean_box(0);
x_648 = lean_box(2);
x_649 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_649, 0, x_615);
x_650 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_650, 0, x_624);
lean_ctor_set(x_650, 1, x_623);
lean_ctor_set(x_650, 2, x_625);
lean_ctor_set(x_650, 3, x_625);
lean_ctor_set_usize(x_650, 4, x_618);
x_651 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_651, 0, x_600);
lean_ctor_set_uint8(x_651, 1, x_600);
lean_ctor_set_uint8(x_651, 2, x_600);
lean_ctor_set_uint8(x_651, 3, x_600);
lean_ctor_set_uint8(x_651, 4, x_600);
x_652 = lean_unbox(x_601);
lean_ctor_set_uint8(x_651, 5, x_652);
x_653 = lean_unbox(x_601);
lean_ctor_set_uint8(x_651, 6, x_653);
lean_ctor_set_uint8(x_651, 7, x_600);
x_654 = lean_unbox(x_601);
lean_ctor_set_uint8(x_651, 8, x_654);
x_655 = lean_unbox(x_646);
lean_ctor_set_uint8(x_651, 9, x_655);
x_656 = lean_unbox(x_647);
lean_ctor_set_uint8(x_651, 10, x_656);
x_657 = lean_unbox(x_601);
lean_ctor_set_uint8(x_651, 11, x_657);
x_658 = lean_unbox(x_601);
lean_ctor_set_uint8(x_651, 12, x_658);
x_659 = lean_unbox(x_601);
lean_ctor_set_uint8(x_651, 13, x_659);
x_660 = lean_unbox(x_648);
lean_ctor_set_uint8(x_651, 14, x_660);
x_661 = lean_unbox(x_601);
lean_ctor_set_uint8(x_651, 15, x_661);
x_662 = lean_unbox(x_601);
lean_ctor_set_uint8(x_651, 16, x_662);
x_663 = lean_unbox(x_601);
lean_ctor_set_uint8(x_651, 17, x_663);
x_664 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_651);
x_665 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_665, 0, x_649);
lean_ctor_set(x_665, 1, x_650);
lean_ctor_set(x_665, 2, x_614);
x_666 = lean_mk_empty_array_with_capacity(x_625);
x_667 = lean_box(0);
x_668 = lean_box(0);
x_669 = l_Lean_ConstantInfo_type(x_73);
x_670 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_670, 0, x_651);
lean_ctor_set(x_670, 1, x_614);
lean_ctor_set(x_670, 2, x_665);
lean_ctor_set(x_670, 3, x_666);
lean_ctor_set(x_670, 4, x_667);
lean_ctor_set(x_670, 5, x_625);
lean_ctor_set(x_670, 6, x_668);
lean_ctor_set_uint64(x_670, sizeof(void*)*7, x_664);
lean_ctor_set_uint8(x_670, sizeof(void*)*7 + 8, x_600);
lean_ctor_set_uint8(x_670, sizeof(void*)*7 + 9, x_600);
lean_ctor_set_uint8(x_670, sizeof(void*)*7 + 10, x_600);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_644);
lean_inc(x_670);
x_671 = l_Lean_Compiler_LCNF_toLCNFType(x_669, x_670, x_644, x_4, x_5, x_645);
if (lean_obj_tag(x_671) == 0)
{
lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; 
x_672 = lean_ctor_get(x_671, 0);
lean_inc(x_672);
x_673 = lean_ctor_get(x_671, 1);
lean_inc(x_673);
lean_dec(x_671);
x_674 = lean_box(x_600);
x_675 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_toDecl___lam__1___boxed), 9, 2);
lean_closure_set(x_675, 0, x_674);
lean_closure_set(x_675, 1, x_601);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_644);
x_676 = l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg(x_612, x_675, x_600, x_670, x_644, x_4, x_5, x_673);
if (lean_obj_tag(x_676) == 0)
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; 
x_677 = lean_ctor_get(x_676, 0);
lean_inc(x_677);
x_678 = lean_ctor_get(x_676, 1);
lean_inc(x_678);
lean_dec(x_676);
lean_inc(x_5);
lean_inc(x_4);
x_679 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames(x_677, x_4, x_5, x_678);
if (lean_obj_tag(x_679) == 0)
{
lean_object* x_680; lean_object* x_681; lean_object* x_682; 
x_680 = lean_ctor_get(x_679, 0);
lean_inc(x_680);
x_681 = lean_ctor_get(x_679, 1);
lean_inc(x_681);
lean_dec(x_679);
lean_inc(x_5);
lean_inc(x_4);
x_682 = l_Lean_Compiler_LCNF_macroInline(x_680, x_4, x_5, x_681);
if (lean_obj_tag(x_682) == 0)
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; 
x_683 = lean_ctor_get(x_682, 0);
lean_inc(x_683);
x_684 = lean_ctor_get(x_682, 1);
lean_inc(x_684);
lean_dec(x_682);
lean_inc(x_5);
lean_inc(x_4);
x_685 = l_Lean_Compiler_LCNF_inlineMatchers(x_683, x_4, x_5, x_684);
if (lean_obj_tag(x_685) == 0)
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; 
x_686 = lean_ctor_get(x_685, 0);
lean_inc(x_686);
x_687 = lean_ctor_get(x_685, 1);
lean_inc(x_687);
lean_dec(x_685);
lean_inc(x_5);
lean_inc(x_4);
x_688 = l_Lean_Compiler_LCNF_macroInline(x_686, x_4, x_5, x_687);
if (lean_obj_tag(x_688) == 0)
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; 
x_689 = lean_ctor_get(x_688, 0);
lean_inc(x_689);
x_690 = lean_ctor_get(x_688, 1);
lean_inc(x_690);
lean_dec(x_688);
x_691 = lean_st_ref_get(x_644, x_690);
lean_dec(x_644);
x_692 = lean_ctor_get(x_691, 1);
lean_inc(x_692);
lean_dec(x_691);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_693 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF(x_689, x_2, x_3, x_4, x_5, x_692);
if (lean_obj_tag(x_693) == 0)
{
lean_object* x_694; 
x_694 = lean_ctor_get(x_693, 0);
lean_inc(x_694);
if (lean_obj_tag(x_694) == 1)
{
lean_object* x_695; 
x_695 = lean_ctor_get(x_694, 1);
lean_inc(x_695);
if (lean_obj_tag(x_695) == 5)
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; 
x_696 = lean_ctor_get(x_693, 1);
lean_inc(x_696);
lean_dec(x_693);
x_697 = lean_ctor_get(x_694, 0);
lean_inc(x_697);
lean_dec(x_694);
if (lean_is_exclusive(x_695)) {
 lean_ctor_release(x_695, 0);
 x_698 = x_695;
} else {
 lean_dec_ref(x_695);
 x_698 = lean_box(0);
}
x_699 = l_Lean_Compiler_LCNF_eraseFunDecl(x_697, x_600, x_2, x_3, x_4, x_5, x_696);
x_700 = lean_ctor_get(x_699, 1);
lean_inc(x_700);
lean_dec(x_699);
x_701 = l_Lean_ConstantInfo_levelParams(x_73);
lean_dec(x_73);
x_702 = lean_ctor_get(x_697, 2);
lean_inc(x_702);
x_703 = lean_ctor_get(x_697, 4);
lean_inc(x_703);
lean_dec(x_697);
if (lean_is_scalar(x_698)) {
 x_704 = lean_alloc_ctor(0, 1, 0);
} else {
 x_704 = x_698;
 lean_ctor_set_tag(x_704, 0);
}
lean_ctor_set(x_704, 0, x_703);
x_705 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_705, 0, x_74);
lean_ctor_set(x_705, 1, x_701);
lean_ctor_set(x_705, 2, x_672);
lean_ctor_set(x_705, 3, x_702);
lean_ctor_set(x_705, 4, x_704);
lean_ctor_set(x_705, 5, x_598);
lean_ctor_set_uint8(x_705, sizeof(void*)*6, x_600);
lean_ctor_set_uint8(x_705, sizeof(void*)*6 + 1, x_76);
x_706 = l_Lean_Compiler_LCNF_Decl_etaExpand(x_705, x_2, x_3, x_4, x_5, x_700);
return x_706;
}
else
{
lean_object* x_707; 
lean_dec(x_695);
x_707 = lean_ctor_get(x_693, 1);
lean_inc(x_707);
lean_dec(x_693);
x_7 = x_76;
x_8 = x_625;
x_9 = x_694;
x_10 = x_73;
x_11 = x_598;
x_12 = x_600;
x_13 = x_74;
x_14 = x_672;
x_15 = x_2;
x_16 = x_3;
x_17 = x_4;
x_18 = x_5;
x_19 = x_707;
goto block_25;
}
}
else
{
lean_object* x_708; 
x_708 = lean_ctor_get(x_693, 1);
lean_inc(x_708);
lean_dec(x_693);
x_7 = x_76;
x_8 = x_625;
x_9 = x_694;
x_10 = x_73;
x_11 = x_598;
x_12 = x_600;
x_13 = x_74;
x_14 = x_672;
x_15 = x_2;
x_16 = x_3;
x_17 = x_4;
x_18 = x_5;
x_19 = x_708;
goto block_25;
}
}
else
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; 
lean_dec(x_672);
lean_dec(x_598);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_709 = lean_ctor_get(x_693, 0);
lean_inc(x_709);
x_710 = lean_ctor_get(x_693, 1);
lean_inc(x_710);
if (lean_is_exclusive(x_693)) {
 lean_ctor_release(x_693, 0);
 lean_ctor_release(x_693, 1);
 x_711 = x_693;
} else {
 lean_dec_ref(x_693);
 x_711 = lean_box(0);
}
if (lean_is_scalar(x_711)) {
 x_712 = lean_alloc_ctor(1, 2, 0);
} else {
 x_712 = x_711;
}
lean_ctor_set(x_712, 0, x_709);
lean_ctor_set(x_712, 1, x_710);
return x_712;
}
}
else
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; 
lean_dec(x_672);
lean_dec(x_644);
lean_dec(x_598);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_713 = lean_ctor_get(x_688, 0);
lean_inc(x_713);
x_714 = lean_ctor_get(x_688, 1);
lean_inc(x_714);
if (lean_is_exclusive(x_688)) {
 lean_ctor_release(x_688, 0);
 lean_ctor_release(x_688, 1);
 x_715 = x_688;
} else {
 lean_dec_ref(x_688);
 x_715 = lean_box(0);
}
if (lean_is_scalar(x_715)) {
 x_716 = lean_alloc_ctor(1, 2, 0);
} else {
 x_716 = x_715;
}
lean_ctor_set(x_716, 0, x_713);
lean_ctor_set(x_716, 1, x_714);
return x_716;
}
}
else
{
lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; 
lean_dec(x_672);
lean_dec(x_644);
lean_dec(x_598);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_717 = lean_ctor_get(x_685, 0);
lean_inc(x_717);
x_718 = lean_ctor_get(x_685, 1);
lean_inc(x_718);
if (lean_is_exclusive(x_685)) {
 lean_ctor_release(x_685, 0);
 lean_ctor_release(x_685, 1);
 x_719 = x_685;
} else {
 lean_dec_ref(x_685);
 x_719 = lean_box(0);
}
if (lean_is_scalar(x_719)) {
 x_720 = lean_alloc_ctor(1, 2, 0);
} else {
 x_720 = x_719;
}
lean_ctor_set(x_720, 0, x_717);
lean_ctor_set(x_720, 1, x_718);
return x_720;
}
}
else
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; 
lean_dec(x_672);
lean_dec(x_644);
lean_dec(x_598);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_721 = lean_ctor_get(x_682, 0);
lean_inc(x_721);
x_722 = lean_ctor_get(x_682, 1);
lean_inc(x_722);
if (lean_is_exclusive(x_682)) {
 lean_ctor_release(x_682, 0);
 lean_ctor_release(x_682, 1);
 x_723 = x_682;
} else {
 lean_dec_ref(x_682);
 x_723 = lean_box(0);
}
if (lean_is_scalar(x_723)) {
 x_724 = lean_alloc_ctor(1, 2, 0);
} else {
 x_724 = x_723;
}
lean_ctor_set(x_724, 0, x_721);
lean_ctor_set(x_724, 1, x_722);
return x_724;
}
}
else
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; 
lean_dec(x_672);
lean_dec(x_644);
lean_dec(x_598);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_725 = lean_ctor_get(x_679, 0);
lean_inc(x_725);
x_726 = lean_ctor_get(x_679, 1);
lean_inc(x_726);
if (lean_is_exclusive(x_679)) {
 lean_ctor_release(x_679, 0);
 lean_ctor_release(x_679, 1);
 x_727 = x_679;
} else {
 lean_dec_ref(x_679);
 x_727 = lean_box(0);
}
if (lean_is_scalar(x_727)) {
 x_728 = lean_alloc_ctor(1, 2, 0);
} else {
 x_728 = x_727;
}
lean_ctor_set(x_728, 0, x_725);
lean_ctor_set(x_728, 1, x_726);
return x_728;
}
}
else
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; 
lean_dec(x_672);
lean_dec(x_644);
lean_dec(x_598);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_729 = lean_ctor_get(x_676, 0);
lean_inc(x_729);
x_730 = lean_ctor_get(x_676, 1);
lean_inc(x_730);
if (lean_is_exclusive(x_676)) {
 lean_ctor_release(x_676, 0);
 lean_ctor_release(x_676, 1);
 x_731 = x_676;
} else {
 lean_dec_ref(x_676);
 x_731 = lean_box(0);
}
if (lean_is_scalar(x_731)) {
 x_732 = lean_alloc_ctor(1, 2, 0);
} else {
 x_732 = x_731;
}
lean_ctor_set(x_732, 0, x_729);
lean_ctor_set(x_732, 1, x_730);
return x_732;
}
}
else
{
lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; 
lean_dec(x_670);
lean_dec(x_644);
lean_dec(x_612);
lean_dec(x_598);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_733 = lean_ctor_get(x_671, 0);
lean_inc(x_733);
x_734 = lean_ctor_get(x_671, 1);
lean_inc(x_734);
if (lean_is_exclusive(x_671)) {
 lean_ctor_release(x_671, 0);
 lean_ctor_release(x_671, 1);
 x_735 = x_671;
} else {
 lean_dec_ref(x_671);
 x_735 = lean_box(0);
}
if (lean_is_scalar(x_735)) {
 x_736 = lean_alloc_ctor(1, 2, 0);
} else {
 x_736 = x_735;
}
lean_ctor_set(x_736, 0, x_733);
lean_ctor_set(x_736, 1, x_734);
return x_736;
}
}
}
else
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; size_t x_741; lean_object* x_742; lean_object* x_743; size_t x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; uint8_t x_776; uint8_t x_777; uint8_t x_778; uint8_t x_779; uint8_t x_780; uint8_t x_781; uint8_t x_782; uint8_t x_783; uint8_t x_784; uint8_t x_785; uint8_t x_786; uint8_t x_787; uint8_t x_788; uint8_t x_789; uint8_t x_790; uint8_t x_791; uint8_t x_792; uint8_t x_793; uint64_t x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; uint8_t x_801; uint8_t x_802; uint8_t x_803; lean_object* x_804; 
x_737 = lean_box(0);
x_738 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_739 = lean_unsigned_to_nat(2u);
x_740 = lean_unsigned_to_nat(5u);
x_741 = lean_usize_of_nat(x_740);
x_742 = lean_usize_to_nat(x_741);
x_743 = lean_nat_pow(x_739, x_742);
lean_dec(x_742);
x_744 = lean_usize_of_nat(x_743);
lean_dec(x_743);
x_745 = lean_usize_to_nat(x_744);
x_746 = lean_mk_empty_array_with_capacity(x_745);
lean_dec(x_745);
lean_inc(x_746);
x_747 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_747, 0, x_746);
x_748 = lean_unsigned_to_nat(0u);
lean_inc(x_738);
x_749 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_749, 0, x_738);
lean_inc(x_738);
x_750 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_750, 0, x_738);
lean_inc(x_738);
x_751 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_751, 0, x_738);
lean_inc(x_738);
x_752 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_752, 0, x_738);
lean_inc(x_738);
x_753 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_753, 0, x_738);
lean_inc(x_738);
x_754 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_754, 0, x_738);
lean_inc(x_749);
x_755 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_755, 0, x_748);
lean_ctor_set(x_755, 1, x_748);
lean_ctor_set(x_755, 2, x_748);
lean_ctor_set(x_755, 3, x_749);
lean_ctor_set(x_755, 4, x_750);
lean_ctor_set(x_755, 5, x_751);
lean_ctor_set(x_755, 6, x_752);
lean_ctor_set(x_755, 7, x_753);
lean_ctor_set(x_755, 8, x_754);
lean_inc(x_738);
x_756 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_756, 0, x_738);
lean_inc(x_738);
x_757 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_757, 0, x_738);
lean_inc(x_738);
x_758 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_758, 0, x_738);
lean_inc(x_738);
x_759 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_759, 0, x_738);
lean_inc(x_759);
lean_inc(x_756);
x_760 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_760, 0, x_756);
lean_ctor_set(x_760, 1, x_757);
lean_ctor_set(x_760, 2, x_758);
lean_ctor_set(x_760, 3, x_756);
lean_ctor_set(x_760, 4, x_759);
lean_ctor_set(x_760, 5, x_759);
lean_inc(x_746);
x_761 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_761, 0, x_746);
lean_inc(x_746);
x_762 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_762, 0, x_761);
lean_ctor_set(x_762, 1, x_746);
lean_ctor_set(x_762, 2, x_748);
lean_ctor_set(x_762, 3, x_748);
lean_ctor_set_usize(x_762, 4, x_741);
lean_inc(x_738);
x_763 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_763, 0, x_738);
lean_inc_n(x_749, 2);
x_764 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_764, 0, x_749);
lean_ctor_set(x_764, 1, x_749);
lean_ctor_set(x_764, 2, x_749);
lean_ctor_set(x_764, 3, x_763);
x_765 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_765, 0, x_755);
lean_ctor_set(x_765, 1, x_760);
lean_ctor_set(x_765, 2, x_737);
lean_ctor_set(x_765, 3, x_762);
lean_ctor_set(x_765, 4, x_764);
x_766 = lean_st_mk_ref(x_765, x_596);
x_767 = lean_ctor_get(x_766, 0);
lean_inc(x_767);
x_768 = lean_ctor_get(x_766, 1);
lean_inc(x_768);
lean_dec(x_766);
x_769 = lean_box(1);
x_770 = lean_box(0);
x_771 = lean_box(2);
x_772 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_772, 0, x_738);
x_773 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_773, 0, x_747);
lean_ctor_set(x_773, 1, x_746);
lean_ctor_set(x_773, 2, x_748);
lean_ctor_set(x_773, 3, x_748);
lean_ctor_set_usize(x_773, 4, x_741);
x_774 = lean_box(0);
x_775 = lean_alloc_ctor(0, 0, 18);
x_776 = lean_unbox(x_774);
lean_ctor_set_uint8(x_775, 0, x_776);
x_777 = lean_unbox(x_774);
lean_ctor_set_uint8(x_775, 1, x_777);
x_778 = lean_unbox(x_774);
lean_ctor_set_uint8(x_775, 2, x_778);
x_779 = lean_unbox(x_774);
lean_ctor_set_uint8(x_775, 3, x_779);
x_780 = lean_unbox(x_774);
lean_ctor_set_uint8(x_775, 4, x_780);
x_781 = lean_unbox(x_601);
lean_ctor_set_uint8(x_775, 5, x_781);
x_782 = lean_unbox(x_601);
lean_ctor_set_uint8(x_775, 6, x_782);
x_783 = lean_unbox(x_774);
lean_ctor_set_uint8(x_775, 7, x_783);
x_784 = lean_unbox(x_601);
lean_ctor_set_uint8(x_775, 8, x_784);
x_785 = lean_unbox(x_769);
lean_ctor_set_uint8(x_775, 9, x_785);
x_786 = lean_unbox(x_770);
lean_ctor_set_uint8(x_775, 10, x_786);
x_787 = lean_unbox(x_601);
lean_ctor_set_uint8(x_775, 11, x_787);
x_788 = lean_unbox(x_601);
lean_ctor_set_uint8(x_775, 12, x_788);
x_789 = lean_unbox(x_601);
lean_ctor_set_uint8(x_775, 13, x_789);
x_790 = lean_unbox(x_771);
lean_ctor_set_uint8(x_775, 14, x_790);
x_791 = lean_unbox(x_601);
lean_ctor_set_uint8(x_775, 15, x_791);
x_792 = lean_unbox(x_601);
lean_ctor_set_uint8(x_775, 16, x_792);
x_793 = lean_unbox(x_601);
lean_ctor_set_uint8(x_775, 17, x_793);
x_794 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_775);
x_795 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_795, 0, x_772);
lean_ctor_set(x_795, 1, x_773);
lean_ctor_set(x_795, 2, x_737);
x_796 = lean_mk_empty_array_with_capacity(x_748);
x_797 = lean_box(0);
x_798 = lean_box(0);
x_799 = l_Lean_ConstantInfo_type(x_73);
x_800 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_800, 0, x_775);
lean_ctor_set(x_800, 1, x_737);
lean_ctor_set(x_800, 2, x_795);
lean_ctor_set(x_800, 3, x_796);
lean_ctor_set(x_800, 4, x_797);
lean_ctor_set(x_800, 5, x_748);
lean_ctor_set(x_800, 6, x_798);
lean_ctor_set_uint64(x_800, sizeof(void*)*7, x_794);
x_801 = lean_unbox(x_774);
lean_ctor_set_uint8(x_800, sizeof(void*)*7 + 8, x_801);
x_802 = lean_unbox(x_774);
lean_ctor_set_uint8(x_800, sizeof(void*)*7 + 9, x_802);
x_803 = lean_unbox(x_774);
lean_ctor_set_uint8(x_800, sizeof(void*)*7 + 10, x_803);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_767);
x_804 = l_Lean_Compiler_LCNF_toLCNFType(x_799, x_800, x_767, x_4, x_5, x_768);
if (lean_obj_tag(x_804) == 0)
{
lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; uint8_t x_809; 
x_805 = lean_ctor_get(x_804, 0);
lean_inc(x_805);
x_806 = lean_ctor_get(x_804, 1);
lean_inc(x_806);
lean_dec(x_804);
x_807 = lean_st_ref_get(x_767, x_806);
lean_dec(x_767);
x_808 = lean_ctor_get(x_807, 1);
lean_inc(x_808);
lean_dec(x_807);
x_809 = lean_unbox(x_774);
x_47 = x_76;
x_48 = x_809;
x_49 = x_73;
x_50 = x_598;
x_51 = x_74;
x_52 = x_805;
x_53 = x_808;
goto block_72;
}
else
{
lean_dec(x_767);
if (lean_obj_tag(x_804) == 0)
{
lean_object* x_810; lean_object* x_811; uint8_t x_812; 
x_810 = lean_ctor_get(x_804, 0);
lean_inc(x_810);
x_811 = lean_ctor_get(x_804, 1);
lean_inc(x_811);
lean_dec(x_804);
x_812 = lean_unbox(x_774);
x_47 = x_76;
x_48 = x_812;
x_49 = x_73;
x_50 = x_598;
x_51 = x_74;
x_52 = x_810;
x_53 = x_811;
goto block_72;
}
else
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; 
lean_dec(x_598);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_813 = lean_ctor_get(x_804, 0);
lean_inc(x_813);
x_814 = lean_ctor_get(x_804, 1);
lean_inc(x_814);
if (lean_is_exclusive(x_804)) {
 lean_ctor_release(x_804, 0);
 lean_ctor_release(x_804, 1);
 x_815 = x_804;
} else {
 lean_dec_ref(x_804);
 x_815 = lean_box(0);
}
if (lean_is_scalar(x_815)) {
 x_816 = lean_alloc_ctor(1, 2, 0);
} else {
 x_816 = x_815;
}
lean_ctor_set(x_816, 0, x_813);
lean_ctor_set(x_816, 1, x_814);
return x_816;
}
}
}
}
else
{
lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; size_t x_823; lean_object* x_824; lean_object* x_825; size_t x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; uint8_t x_859; uint8_t x_860; uint8_t x_861; uint8_t x_862; uint8_t x_863; uint8_t x_864; uint8_t x_865; uint8_t x_866; uint8_t x_867; uint8_t x_868; uint8_t x_869; uint8_t x_870; uint8_t x_871; uint8_t x_872; uint8_t x_873; uint8_t x_874; uint8_t x_875; uint8_t x_876; uint64_t x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; uint8_t x_884; uint8_t x_885; uint8_t x_886; lean_object* x_887; 
lean_dec(x_597);
x_817 = lean_ctor_get(x_599, 0);
lean_inc(x_817);
if (lean_is_exclusive(x_599)) {
 lean_ctor_release(x_599, 0);
 x_818 = x_599;
} else {
 lean_dec_ref(x_599);
 x_818 = lean_box(0);
}
x_819 = lean_box(0);
x_820 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_821 = lean_unsigned_to_nat(2u);
x_822 = lean_unsigned_to_nat(5u);
x_823 = lean_usize_of_nat(x_822);
x_824 = lean_usize_to_nat(x_823);
x_825 = lean_nat_pow(x_821, x_824);
lean_dec(x_824);
x_826 = lean_usize_of_nat(x_825);
lean_dec(x_825);
x_827 = lean_usize_to_nat(x_826);
x_828 = lean_mk_empty_array_with_capacity(x_827);
lean_dec(x_827);
lean_inc(x_828);
if (lean_is_scalar(x_818)) {
 x_829 = lean_alloc_ctor(0, 1, 0);
} else {
 x_829 = x_818;
 lean_ctor_set_tag(x_829, 0);
}
lean_ctor_set(x_829, 0, x_828);
x_830 = lean_unsigned_to_nat(0u);
lean_inc(x_820);
x_831 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_831, 0, x_820);
lean_inc(x_820);
x_832 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_832, 0, x_820);
lean_inc(x_820);
x_833 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_833, 0, x_820);
lean_inc(x_820);
x_834 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_834, 0, x_820);
lean_inc(x_820);
x_835 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_835, 0, x_820);
lean_inc(x_820);
x_836 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_836, 0, x_820);
lean_inc(x_831);
x_837 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_837, 0, x_830);
lean_ctor_set(x_837, 1, x_830);
lean_ctor_set(x_837, 2, x_830);
lean_ctor_set(x_837, 3, x_831);
lean_ctor_set(x_837, 4, x_832);
lean_ctor_set(x_837, 5, x_833);
lean_ctor_set(x_837, 6, x_834);
lean_ctor_set(x_837, 7, x_835);
lean_ctor_set(x_837, 8, x_836);
lean_inc(x_820);
x_838 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_838, 0, x_820);
lean_inc(x_820);
x_839 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_839, 0, x_820);
lean_inc(x_820);
x_840 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_840, 0, x_820);
lean_inc(x_820);
x_841 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_841, 0, x_820);
lean_inc(x_841);
lean_inc(x_838);
x_842 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_842, 0, x_838);
lean_ctor_set(x_842, 1, x_839);
lean_ctor_set(x_842, 2, x_840);
lean_ctor_set(x_842, 3, x_838);
lean_ctor_set(x_842, 4, x_841);
lean_ctor_set(x_842, 5, x_841);
lean_inc(x_828);
x_843 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_843, 0, x_828);
lean_inc(x_828);
x_844 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_844, 0, x_843);
lean_ctor_set(x_844, 1, x_828);
lean_ctor_set(x_844, 2, x_830);
lean_ctor_set(x_844, 3, x_830);
lean_ctor_set_usize(x_844, 4, x_823);
lean_inc(x_820);
x_845 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_845, 0, x_820);
lean_inc_n(x_831, 2);
x_846 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_846, 0, x_831);
lean_ctor_set(x_846, 1, x_831);
lean_ctor_set(x_846, 2, x_831);
lean_ctor_set(x_846, 3, x_845);
x_847 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_847, 0, x_837);
lean_ctor_set(x_847, 1, x_842);
lean_ctor_set(x_847, 2, x_819);
lean_ctor_set(x_847, 3, x_844);
lean_ctor_set(x_847, 4, x_846);
x_848 = lean_st_mk_ref(x_847, x_596);
x_849 = lean_ctor_get(x_848, 0);
lean_inc(x_849);
x_850 = lean_ctor_get(x_848, 1);
lean_inc(x_850);
lean_dec(x_848);
x_851 = lean_box(1);
x_852 = lean_box(1);
x_853 = lean_box(0);
x_854 = lean_box(2);
x_855 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_855, 0, x_820);
x_856 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_856, 0, x_829);
lean_ctor_set(x_856, 1, x_828);
lean_ctor_set(x_856, 2, x_830);
lean_ctor_set(x_856, 3, x_830);
lean_ctor_set_usize(x_856, 4, x_823);
x_857 = lean_box(0);
x_858 = lean_alloc_ctor(0, 0, 18);
x_859 = lean_unbox(x_857);
lean_ctor_set_uint8(x_858, 0, x_859);
x_860 = lean_unbox(x_857);
lean_ctor_set_uint8(x_858, 1, x_860);
x_861 = lean_unbox(x_857);
lean_ctor_set_uint8(x_858, 2, x_861);
x_862 = lean_unbox(x_857);
lean_ctor_set_uint8(x_858, 3, x_862);
x_863 = lean_unbox(x_857);
lean_ctor_set_uint8(x_858, 4, x_863);
x_864 = lean_unbox(x_851);
lean_ctor_set_uint8(x_858, 5, x_864);
x_865 = lean_unbox(x_851);
lean_ctor_set_uint8(x_858, 6, x_865);
x_866 = lean_unbox(x_857);
lean_ctor_set_uint8(x_858, 7, x_866);
x_867 = lean_unbox(x_851);
lean_ctor_set_uint8(x_858, 8, x_867);
x_868 = lean_unbox(x_852);
lean_ctor_set_uint8(x_858, 9, x_868);
x_869 = lean_unbox(x_853);
lean_ctor_set_uint8(x_858, 10, x_869);
x_870 = lean_unbox(x_851);
lean_ctor_set_uint8(x_858, 11, x_870);
x_871 = lean_unbox(x_851);
lean_ctor_set_uint8(x_858, 12, x_871);
x_872 = lean_unbox(x_851);
lean_ctor_set_uint8(x_858, 13, x_872);
x_873 = lean_unbox(x_854);
lean_ctor_set_uint8(x_858, 14, x_873);
x_874 = lean_unbox(x_851);
lean_ctor_set_uint8(x_858, 15, x_874);
x_875 = lean_unbox(x_851);
lean_ctor_set_uint8(x_858, 16, x_875);
x_876 = lean_unbox(x_851);
lean_ctor_set_uint8(x_858, 17, x_876);
x_877 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_858);
x_878 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_878, 0, x_855);
lean_ctor_set(x_878, 1, x_856);
lean_ctor_set(x_878, 2, x_819);
x_879 = lean_mk_empty_array_with_capacity(x_830);
x_880 = lean_box(0);
x_881 = lean_box(0);
x_882 = l_Lean_ConstantInfo_type(x_73);
x_883 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_883, 0, x_858);
lean_ctor_set(x_883, 1, x_819);
lean_ctor_set(x_883, 2, x_878);
lean_ctor_set(x_883, 3, x_879);
lean_ctor_set(x_883, 4, x_880);
lean_ctor_set(x_883, 5, x_830);
lean_ctor_set(x_883, 6, x_881);
lean_ctor_set_uint64(x_883, sizeof(void*)*7, x_877);
x_884 = lean_unbox(x_857);
lean_ctor_set_uint8(x_883, sizeof(void*)*7 + 8, x_884);
x_885 = lean_unbox(x_857);
lean_ctor_set_uint8(x_883, sizeof(void*)*7 + 9, x_885);
x_886 = lean_unbox(x_857);
lean_ctor_set_uint8(x_883, sizeof(void*)*7 + 10, x_886);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_849);
x_887 = l_Lean_Compiler_LCNF_toLCNFType(x_882, x_883, x_849, x_4, x_5, x_850);
if (lean_obj_tag(x_887) == 0)
{
lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; uint8_t x_892; 
x_888 = lean_ctor_get(x_887, 0);
lean_inc(x_888);
x_889 = lean_ctor_get(x_887, 1);
lean_inc(x_889);
lean_dec(x_887);
x_890 = lean_st_ref_get(x_849, x_889);
lean_dec(x_849);
x_891 = lean_ctor_get(x_890, 1);
lean_inc(x_891);
lean_dec(x_890);
x_892 = lean_unbox(x_857);
x_26 = x_76;
x_27 = x_817;
x_28 = x_73;
x_29 = x_598;
x_30 = x_74;
x_31 = x_892;
x_32 = x_888;
x_33 = x_891;
goto block_46;
}
else
{
lean_dec(x_849);
if (lean_obj_tag(x_887) == 0)
{
lean_object* x_893; lean_object* x_894; uint8_t x_895; 
x_893 = lean_ctor_get(x_887, 0);
lean_inc(x_893);
x_894 = lean_ctor_get(x_887, 1);
lean_inc(x_894);
lean_dec(x_887);
x_895 = lean_unbox(x_857);
x_26 = x_76;
x_27 = x_817;
x_28 = x_73;
x_29 = x_598;
x_30 = x_74;
x_31 = x_895;
x_32 = x_893;
x_33 = x_894;
goto block_46;
}
else
{
lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; 
lean_dec(x_817);
lean_dec(x_598);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_896 = lean_ctor_get(x_887, 0);
lean_inc(x_896);
x_897 = lean_ctor_get(x_887, 1);
lean_inc(x_897);
if (lean_is_exclusive(x_887)) {
 lean_ctor_release(x_887, 0);
 lean_ctor_release(x_887, 1);
 x_898 = x_887;
} else {
 lean_dec_ref(x_887);
 x_898 = lean_box(0);
}
if (lean_is_scalar(x_898)) {
 x_899 = lean_alloc_ctor(1, 2, 0);
} else {
 x_899 = x_898;
}
lean_ctor_set(x_899, 0, x_896);
lean_ctor_set(x_899, 1, x_897);
return x_899;
}
}
}
}
}
block_931:
{
lean_object* x_902; lean_object* x_903; 
lean_inc(x_901);
x_902 = l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg(x_901, x_5, x_6);
x_903 = lean_ctor_get(x_902, 0);
lean_inc(x_903);
if (lean_obj_tag(x_903) == 0)
{
uint8_t x_904; 
x_904 = !lean_is_exclusive(x_902);
if (x_904 == 0)
{
lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; 
x_905 = lean_ctor_get(x_902, 1);
x_906 = lean_ctor_get(x_902, 0);
lean_dec(x_906);
x_907 = lean_mk_string_unchecked("declaration `", 13, 13);
x_908 = l_Lean_stringToMessageData(x_907);
lean_dec(x_907);
x_909 = l_Lean_MessageData_ofName(x_901);
lean_ctor_set_tag(x_902, 7);
lean_ctor_set(x_902, 1, x_909);
lean_ctor_set(x_902, 0, x_908);
x_910 = lean_mk_string_unchecked("` not found", 11, 11);
x_911 = l_Lean_stringToMessageData(x_910);
lean_dec(x_910);
x_912 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_912, 0, x_902);
lean_ctor_set(x_912, 1, x_911);
x_913 = l_Lean_throwError___at___Lean_Compiler_LCNF_getType_spec__1(lean_box(0), x_912, x_2, x_3, x_4, x_5, x_905);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_913;
}
else
{
lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; 
x_914 = lean_ctor_get(x_902, 1);
lean_inc(x_914);
lean_dec(x_902);
x_915 = lean_mk_string_unchecked("declaration `", 13, 13);
x_916 = l_Lean_stringToMessageData(x_915);
lean_dec(x_915);
x_917 = l_Lean_MessageData_ofName(x_901);
x_918 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_918, 0, x_916);
lean_ctor_set(x_918, 1, x_917);
x_919 = lean_mk_string_unchecked("` not found", 11, 11);
x_920 = l_Lean_stringToMessageData(x_919);
lean_dec(x_919);
x_921 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_921, 0, x_918);
lean_ctor_set(x_921, 1, x_920);
x_922 = l_Lean_throwError___at___Lean_Compiler_LCNF_getType_spec__1(lean_box(0), x_921, x_2, x_3, x_4, x_5, x_914);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_922;
}
}
else
{
lean_object* x_923; lean_object* x_924; uint8_t x_925; 
x_923 = lean_ctor_get(x_902, 1);
lean_inc(x_923);
lean_dec(x_902);
x_924 = lean_ctor_get(x_903, 0);
lean_inc(x_924);
lean_dec(x_903);
x_925 = l_Lean_ConstantInfo_isPartial(x_924);
if (x_925 == 0)
{
uint8_t x_926; 
x_926 = l_Lean_ConstantInfo_isUnsafe(x_924);
if (x_926 == 0)
{
lean_object* x_927; uint8_t x_928; 
x_927 = lean_box(1);
x_928 = lean_unbox(x_927);
x_73 = x_924;
x_74 = x_901;
x_75 = x_923;
x_76 = x_928;
goto block_900;
}
else
{
x_73 = x_924;
x_74 = x_901;
x_75 = x_923;
x_76 = x_925;
goto block_900;
}
}
else
{
lean_object* x_929; uint8_t x_930; 
x_929 = lean_box(0);
x_930 = lean_unbox(x_929);
x_73 = x_924;
x_74 = x_901;
x_75 = x_923;
x_76 = x_930;
goto block_900;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Compiler_LCNF_toDecl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Loop_forIn_loop___at___Lean_Compiler_LCNF_toDecl_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_toDecl___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_Compiler_LCNF_toDecl___lam__1(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
}
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_ExternAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_InitAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_ImplementedByAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_ToLCNF(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ToDecl(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Transform(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatcherInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ExternAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_InitAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ImplementedByAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ToLCNF(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
