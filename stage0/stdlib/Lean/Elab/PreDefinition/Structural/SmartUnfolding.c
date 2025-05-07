// Lean compiler output
// Module: Lean.Elab.PreDefinition.Structural.SmartUnfolding
// Imports: Lean.Elab.PreDefinition.Basic Lean.Elab.PreDefinition.Structural.Basic Lean.Meta.Match.MatcherApp.Basic
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__8___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDef___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addNonRec(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__9___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_markSmartUnfoldingMatchAlt(lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__7___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__8___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_markSmartUnfoldingMatch(lean_object*);
lean_object* l_Lean_Elab_withEnableInfoTree___at___Lean_Elab_addAndCompilePartialRec_spec__2___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
uint8_t l_Lean_Elab_Structural_recArgHasLooseBVarsAt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Array_extract(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___redArg(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDef___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_toExpr(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__8___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_smartUnfoldingMatch_x3f(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__8___lam__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_reduceMatcher_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_List_lengthTR(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3_spec__4_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_uget(x_5, x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit(x_1, x_2, x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = lean_array_uset(x_5, x_4, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_usize_of_nat(x_19);
x_21 = lean_usize_add(x_4, x_20);
x_22 = lean_array_uset(x_18, x_4, x_15);
x_4 = x_21;
x_5 = x_22;
x_10 = x_16;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_array_set(x_4, x_5, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_5, x_14);
lean_dec(x_5);
x_3 = x_11;
x_4 = x_13;
x_5 = x_15;
goto _start;
}
else
{
lean_object* x_17; 
lean_dec(x_5);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_17 = l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit(x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; size_t x_20; lean_object* x_21; size_t x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_array_size(x_4);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_usize_of_nat(x_21);
x_23 = l_Array_mapMUnsafe_map___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__0(x_1, x_2, x_20, x_22, x_4, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = l_Lean_mkAppN(x_18, x_25);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_29 = l_Lean_mkAppN(x_18, x_27);
lean_dec(x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_18);
x_31 = !lean_is_exclusive(x_23);
if (x_31 == 0)
{
return x_23;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_23, 0);
x_33 = lean_ctor_get(x_23, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_23);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_array_set(x_4, x_5, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_5, x_14);
x_16 = l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__1_spec__1(x_1, x_2, x_11, x_13, x_15, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
else
{
lean_object* x_17; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_17 = l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit(x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; size_t x_20; lean_object* x_21; size_t x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_array_size(x_4);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_usize_of_nat(x_21);
x_23 = l_Array_mapMUnsafe_map___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__0(x_1, x_2, x_20, x_22, x_4, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = l_Lean_mkAppN(x_18, x_25);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_29 = l_Lean_mkAppN(x_18, x_27);
lean_dec(x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_18);
x_31 = !lean_is_exclusive(x_23);
if (x_31 == 0)
{
return x_23;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_23, 0);
x_33 = lean_ctor_get(x_23, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_23);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 0);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 0);
x_9 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
x_10 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
x_11 = l_instMonadEIO(lean_box(0));
x_12 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_14);
x_15 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_16, 0, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_closure((void*)(l_instMonadEIO___lam__1), 5, 0);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_alloc_closure((void*)(l_instMonadEIO___lam__2), 5, 0);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_24, 0, lean_box(0));
lean_closure_set(x_24, 1, lean_box(0));
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_26, 0, x_25);
lean_inc(x_26);
lean_inc(x_23);
lean_inc(x_20);
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_9);
lean_ctor_set(x_27, 2, x_20);
lean_ctor_set(x_27, 3, x_23);
lean_ctor_set(x_27, 4, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_10);
x_29 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
lean_inc(x_31);
x_32 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_32, 0, x_31);
x_33 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_33, 0, x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_35, 0, x_20);
x_36 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_36, 0, x_35);
x_37 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_37, 0, x_23);
x_38 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_38, 0, x_37);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_39, 0, x_26);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_41, 0, x_34);
lean_ctor_set(x_41, 1, x_7);
lean_ctor_set(x_41, 2, x_36);
lean_ctor_set(x_41, 3, x_38);
lean_ctor_set(x_41, 4, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_8);
x_43 = lean_box(0);
x_44 = l_instInhabitedOfMonad___redArg(x_42, x_43);
x_45 = lean_panic_fn(x_44, x_1);
x_46 = lean_apply_5(x_45, x_2, x_3, x_4, x_5, x_6);
return x_46;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3_spec__4_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 6)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_14, 4);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_array_push(x_2, x_15);
x_1 = x_10;
x_2 = x_16;
x_7 = x_13;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_12);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_mk_string_unchecked("Lean.Meta.Match.MatcherApp.Basic", 32, 32);
x_20 = lean_mk_string_unchecked("Lean.Meta.matchMatcherApp\?", 26, 26);
x_21 = lean_unsigned_to_nat(63u);
x_22 = lean_unsigned_to_nat(53u);
x_23 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_24 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_19, x_20, x_21, x_22, x_23);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_25 = l_panic___at___Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3_spec__3(x_24, x_3, x_4, x_5, x_6, x_18);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_1 = x_10;
x_7 = x_26;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 0);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_25);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_11);
if (x_32 == 0)
{
return x_11;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_11, 0);
x_34 = lean_ctor_get(x_11, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_11);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3_spec__4_spec__4___redArg(x_2, x_3, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_10, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 6)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_15, 4);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_array_push(x_3, x_16);
x_18 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3_spec__4_spec__4___redArg(x_11, x_17, x_4, x_5, x_6, x_7, x_14);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_13);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_mk_string_unchecked("Lean.Meta.Match.MatcherApp.Basic", 32, 32);
x_21 = lean_mk_string_unchecked("Lean.Meta.matchMatcherApp\?", 26, 26);
x_22 = lean_unsigned_to_nat(63u);
x_23 = lean_unsigned_to_nat(53u);
x_24 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_25 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_20, x_21, x_22, x_23, x_24);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_26 = l_panic___at___Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3_spec__3(x_25, x_4, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3_spec__4_spec__4___redArg(x_11, x_3, x_4, x_5, x_6, x_7, x_27);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_26);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_33 = !lean_is_exclusive(x_12);
if (x_33 == 0)
{
return x_12;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_12, 0);
x_35 = lean_ctor_get(x_12, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_12);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3_spec__4___redArg(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_apply_6(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3___lam__0___boxed), 6, 0);
x_9 = l_Lean_Expr_getAppFn(x_1);
switch (lean_obj_tag(x_9)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Expr_bvar___override(x_10);
x_12 = l_Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3___lam__1(x_8, x_11, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = l_Lean_Expr_fvar___override(x_13);
x_15 = l_Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3___lam__1(x_8, x_14, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_14);
return x_15;
}
case 2:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
x_17 = l_Lean_Expr_mvar___override(x_16);
x_18 = l_Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3___lam__1(x_8, x_17, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_17);
return x_18;
}
case 3:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_19 = lean_ctor_get(x_9, 0);
lean_inc(x_19);
lean_dec(x_9);
x_20 = l_Lean_Expr_sort___override(x_19);
x_21 = l_Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3___lam__1(x_8, x_20, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_20);
return x_21;
}
case 4:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_8);
x_22 = lean_ctor_get(x_9, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_dec(x_9);
lean_inc(x_22);
x_24 = l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_reduceMatcher_x3f_spec__0___redArg(x_22, x_6, x_7);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_st_ref_get(x_6, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
if (x_2 == 0)
{
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_1);
goto block_32;
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
lean_dec(x_28);
lean_inc(x_22);
x_34 = l_Lean_isCasesOnRecursor(x_33, x_22);
if (x_34 == 0)
{
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_1);
goto block_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_Lean_Name_getPrefix(x_22);
x_36 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_35, x_3, x_4, x_5, x_6, x_29);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 5)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_39 = lean_ctor_get(x_36, 1);
x_40 = lean_ctor_get(x_36, 0);
lean_dec(x_40);
x_41 = lean_ctor_get(x_37, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 x_42 = x_37;
} else {
 lean_dec_ref(x_37);
 x_42 = lean_box(0);
}
x_43 = lean_box(0);
x_44 = l_Lean_Expr_sort___override(x_43);
x_45 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_45);
x_46 = lean_mk_array(x_45, x_44);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_sub(x_45, x_47);
lean_dec(x_45);
x_49 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_46, x_48);
x_50 = lean_ctor_get(x_41, 1);
lean_inc(x_50);
x_51 = lean_nat_add(x_50, x_47);
x_52 = lean_ctor_get(x_41, 2);
lean_inc(x_52);
x_53 = lean_nat_add(x_51, x_52);
x_54 = lean_nat_add(x_53, x_47);
lean_dec(x_53);
x_55 = l_Lean_InductiveVal_numCtors(x_41);
x_56 = lean_nat_add(x_54, x_55);
lean_dec(x_55);
x_57 = lean_array_get_size(x_49);
x_58 = lean_nat_dec_le(x_56, x_57);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_59 = lean_box(0);
lean_ctor_set(x_36, 0, x_59);
return x_36;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_98; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
lean_free_object(x_36);
x_60 = lean_unsigned_to_nat(0u);
lean_inc(x_50);
lean_inc(x_49);
x_61 = l_Array_toSubarray___redArg(x_49, x_60, x_50);
x_62 = l_Lean_instInhabitedExpr;
x_63 = lean_array_get(x_62, x_49, x_50);
lean_dec(x_50);
lean_inc(x_54);
lean_inc(x_49);
x_64 = l_Array_toSubarray___redArg(x_49, x_51, x_54);
x_65 = lean_nat_add(x_52, x_47);
lean_dec(x_52);
x_66 = lean_box(0);
x_67 = lean_mk_array(x_65, x_66);
lean_inc(x_56);
lean_inc(x_49);
x_68 = l_Array_toSubarray___redArg(x_49, x_54, x_56);
x_69 = l_Array_toSubarray___redArg(x_49, x_56, x_57);
x_102 = lean_ctor_get(x_41, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_104 = l_List_lengthTR(lean_box(0), x_103);
lean_dec(x_103);
x_105 = l_List_lengthTR(lean_box(0), x_23);
x_106 = lean_nat_dec_eq(x_104, x_105);
lean_dec(x_105);
lean_dec(x_104);
if (x_106 == 0)
{
x_98 = x_106;
goto block_101;
}
else
{
x_98 = x_58;
goto block_101;
}
block_97:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_mk_empty_array_with_capacity(x_60);
x_72 = lean_ctor_get(x_41, 4);
lean_inc(x_72);
lean_dec(x_41);
lean_inc(x_72);
x_73 = l_List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3_spec__4___redArg(x_72, x_72, x_71, x_3, x_4, x_5, x_6, x_39);
lean_dec(x_72);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = lean_array_mk(x_23);
x_77 = l_Array_ofSubarray___redArg(x_61);
lean_dec(x_61);
x_78 = l_Array_ofSubarray___redArg(x_64);
lean_dec(x_64);
x_79 = l_Array_ofSubarray___redArg(x_68);
lean_dec(x_68);
x_80 = l_Array_ofSubarray___redArg(x_69);
lean_dec(x_69);
x_81 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_81, 0, x_22);
lean_ctor_set(x_81, 1, x_76);
lean_ctor_set(x_81, 2, x_70);
lean_ctor_set(x_81, 3, x_67);
lean_ctor_set(x_81, 4, x_77);
lean_ctor_set(x_81, 5, x_63);
lean_ctor_set(x_81, 6, x_78);
lean_ctor_set(x_81, 7, x_75);
lean_ctor_set(x_81, 8, x_79);
lean_ctor_set(x_81, 9, x_80);
if (lean_is_scalar(x_42)) {
 x_82 = lean_alloc_ctor(1, 1, 0);
} else {
 x_82 = x_42;
 lean_ctor_set_tag(x_82, 1);
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_73, 0, x_82);
return x_73;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_83 = lean_ctor_get(x_73, 0);
x_84 = lean_ctor_get(x_73, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_73);
x_85 = lean_array_mk(x_23);
x_86 = l_Array_ofSubarray___redArg(x_61);
lean_dec(x_61);
x_87 = l_Array_ofSubarray___redArg(x_64);
lean_dec(x_64);
x_88 = l_Array_ofSubarray___redArg(x_68);
lean_dec(x_68);
x_89 = l_Array_ofSubarray___redArg(x_69);
lean_dec(x_69);
x_90 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_90, 0, x_22);
lean_ctor_set(x_90, 1, x_85);
lean_ctor_set(x_90, 2, x_70);
lean_ctor_set(x_90, 3, x_67);
lean_ctor_set(x_90, 4, x_86);
lean_ctor_set(x_90, 5, x_63);
lean_ctor_set(x_90, 6, x_87);
lean_ctor_set(x_90, 7, x_83);
lean_ctor_set(x_90, 8, x_88);
lean_ctor_set(x_90, 9, x_89);
if (lean_is_scalar(x_42)) {
 x_91 = lean_alloc_ctor(1, 1, 0);
} else {
 x_91 = x_42;
 lean_ctor_set_tag(x_91, 1);
}
lean_ctor_set(x_91, 0, x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_84);
return x_92;
}
}
else
{
uint8_t x_93; 
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_61);
lean_dec(x_42);
lean_dec(x_23);
lean_dec(x_22);
x_93 = !lean_is_exclusive(x_73);
if (x_93 == 0)
{
return x_73;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_73, 0);
x_95 = lean_ctor_get(x_73, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_73);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
block_101:
{
if (x_98 == 0)
{
lean_object* x_99; 
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_60);
x_70 = x_99;
goto block_97;
}
else
{
lean_object* x_100; 
x_100 = lean_box(0);
x_70 = x_100;
goto block_97;
}
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_107 = lean_ctor_get(x_36, 1);
lean_inc(x_107);
lean_dec(x_36);
x_108 = lean_ctor_get(x_37, 0);
lean_inc(x_108);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 x_109 = x_37;
} else {
 lean_dec_ref(x_37);
 x_109 = lean_box(0);
}
x_110 = lean_box(0);
x_111 = l_Lean_Expr_sort___override(x_110);
x_112 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_112);
x_113 = lean_mk_array(x_112, x_111);
x_114 = lean_unsigned_to_nat(1u);
x_115 = lean_nat_sub(x_112, x_114);
lean_dec(x_112);
x_116 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_113, x_115);
x_117 = lean_ctor_get(x_108, 1);
lean_inc(x_117);
x_118 = lean_nat_add(x_117, x_114);
x_119 = lean_ctor_get(x_108, 2);
lean_inc(x_119);
x_120 = lean_nat_add(x_118, x_119);
x_121 = lean_nat_add(x_120, x_114);
lean_dec(x_120);
x_122 = l_Lean_InductiveVal_numCtors(x_108);
x_123 = lean_nat_add(x_121, x_122);
lean_dec(x_122);
x_124 = lean_array_get_size(x_116);
x_125 = lean_nat_dec_le(x_123, x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_121);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_126 = lean_box(0);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_107);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_158; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_128 = lean_unsigned_to_nat(0u);
lean_inc(x_117);
lean_inc(x_116);
x_129 = l_Array_toSubarray___redArg(x_116, x_128, x_117);
x_130 = l_Lean_instInhabitedExpr;
x_131 = lean_array_get(x_130, x_116, x_117);
lean_dec(x_117);
lean_inc(x_121);
lean_inc(x_116);
x_132 = l_Array_toSubarray___redArg(x_116, x_118, x_121);
x_133 = lean_nat_add(x_119, x_114);
lean_dec(x_119);
x_134 = lean_box(0);
x_135 = lean_mk_array(x_133, x_134);
lean_inc(x_123);
lean_inc(x_116);
x_136 = l_Array_toSubarray___redArg(x_116, x_121, x_123);
x_137 = l_Array_toSubarray___redArg(x_116, x_123, x_124);
x_162 = lean_ctor_get(x_108, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
x_164 = l_List_lengthTR(lean_box(0), x_163);
lean_dec(x_163);
x_165 = l_List_lengthTR(lean_box(0), x_23);
x_166 = lean_nat_dec_eq(x_164, x_165);
lean_dec(x_165);
lean_dec(x_164);
if (x_166 == 0)
{
x_158 = x_166;
goto block_161;
}
else
{
x_158 = x_125;
goto block_161;
}
block_157:
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_mk_empty_array_with_capacity(x_128);
x_140 = lean_ctor_get(x_108, 4);
lean_inc(x_140);
lean_dec(x_108);
lean_inc(x_140);
x_141 = l_List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3_spec__4___redArg(x_140, x_140, x_139, x_3, x_4, x_5, x_6, x_107);
lean_dec(x_140);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_144 = x_141;
} else {
 lean_dec_ref(x_141);
 x_144 = lean_box(0);
}
x_145 = lean_array_mk(x_23);
x_146 = l_Array_ofSubarray___redArg(x_129);
lean_dec(x_129);
x_147 = l_Array_ofSubarray___redArg(x_132);
lean_dec(x_132);
x_148 = l_Array_ofSubarray___redArg(x_136);
lean_dec(x_136);
x_149 = l_Array_ofSubarray___redArg(x_137);
lean_dec(x_137);
x_150 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_150, 0, x_22);
lean_ctor_set(x_150, 1, x_145);
lean_ctor_set(x_150, 2, x_138);
lean_ctor_set(x_150, 3, x_135);
lean_ctor_set(x_150, 4, x_146);
lean_ctor_set(x_150, 5, x_131);
lean_ctor_set(x_150, 6, x_147);
lean_ctor_set(x_150, 7, x_142);
lean_ctor_set(x_150, 8, x_148);
lean_ctor_set(x_150, 9, x_149);
if (lean_is_scalar(x_109)) {
 x_151 = lean_alloc_ctor(1, 1, 0);
} else {
 x_151 = x_109;
 lean_ctor_set_tag(x_151, 1);
}
lean_ctor_set(x_151, 0, x_150);
if (lean_is_scalar(x_144)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_144;
}
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_143);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_129);
lean_dec(x_109);
lean_dec(x_23);
lean_dec(x_22);
x_153 = lean_ctor_get(x_141, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_141, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_155 = x_141;
} else {
 lean_dec_ref(x_141);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 2, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_154);
return x_156;
}
}
block_161:
{
if (x_158 == 0)
{
lean_object* x_159; 
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_128);
x_138 = x_159;
goto block_157;
}
else
{
lean_object* x_160; 
x_160 = lean_box(0);
x_138 = x_160;
goto block_157;
}
}
}
}
}
else
{
uint8_t x_167; 
lean_dec(x_37);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_167 = !lean_is_exclusive(x_36);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_36, 0);
lean_dec(x_168);
x_169 = lean_box(0);
lean_ctor_set(x_36, 0, x_169);
return x_36;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_36, 1);
lean_inc(x_170);
lean_dec(x_36);
x_171 = lean_box(0);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
}
}
else
{
uint8_t x_173; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_173 = !lean_is_exclusive(x_36);
if (x_173 == 0)
{
return x_36;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_36, 0);
x_175 = lean_ctor_get(x_36, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_36);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
}
}
block_32:
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_box(0);
x_31 = l_Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3___lam__0(x_30, x_3, x_4, x_5, x_6, x_29);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_31;
}
}
else
{
uint8_t x_177; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_177 = !lean_is_exclusive(x_24);
if (x_177 == 0)
{
lean_object* x_178; uint8_t x_179; 
x_178 = lean_ctor_get(x_24, 0);
lean_dec(x_178);
x_179 = !lean_is_exclusive(x_25);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_180 = lean_ctor_get(x_25, 0);
x_181 = lean_box(0);
x_182 = l_Lean_Expr_sort___override(x_181);
x_183 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_183);
x_184 = lean_mk_array(x_183, x_182);
x_185 = lean_unsigned_to_nat(1u);
x_186 = lean_nat_sub(x_183, x_185);
lean_dec(x_183);
x_187 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_184, x_186);
x_188 = lean_array_get_size(x_187);
x_189 = l_Lean_Meta_Match_MatcherInfo_arity(x_180);
x_190 = lean_nat_dec_lt(x_188, x_189);
lean_dec(x_189);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_191 = lean_array_mk(x_23);
x_192 = lean_ctor_get(x_180, 3);
lean_inc(x_192);
x_193 = lean_ctor_get(x_180, 4);
lean_inc(x_193);
x_194 = lean_unsigned_to_nat(0u);
x_195 = lean_ctor_get(x_180, 0);
lean_inc(x_195);
lean_inc(x_195);
x_196 = l_Array_extract(lean_box(0), x_187, x_194, x_195);
x_197 = l_Lean_instInhabitedExpr;
x_198 = lean_array_get(x_197, x_187, x_195);
x_199 = lean_nat_add(x_195, x_185);
lean_dec(x_195);
x_200 = lean_ctor_get(x_180, 1);
lean_inc(x_200);
x_201 = lean_nat_add(x_199, x_200);
lean_dec(x_200);
lean_inc(x_201);
lean_inc(x_187);
x_202 = l_Array_toSubarray___redArg(x_187, x_199, x_201);
x_203 = l_Array_ofSubarray___redArg(x_202);
lean_dec(x_202);
x_204 = lean_ctor_get(x_180, 2);
lean_inc(x_204);
x_205 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_180);
lean_dec(x_180);
x_206 = lean_nat_add(x_201, x_205);
lean_dec(x_205);
lean_inc(x_206);
lean_inc(x_187);
x_207 = l_Array_toSubarray___redArg(x_187, x_201, x_206);
x_208 = l_Array_ofSubarray___redArg(x_207);
lean_dec(x_207);
x_209 = l_Array_toSubarray___redArg(x_187, x_206, x_188);
x_210 = l_Array_ofSubarray___redArg(x_209);
lean_dec(x_209);
x_211 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_211, 0, x_22);
lean_ctor_set(x_211, 1, x_191);
lean_ctor_set(x_211, 2, x_192);
lean_ctor_set(x_211, 3, x_193);
lean_ctor_set(x_211, 4, x_196);
lean_ctor_set(x_211, 5, x_198);
lean_ctor_set(x_211, 6, x_203);
lean_ctor_set(x_211, 7, x_204);
lean_ctor_set(x_211, 8, x_208);
lean_ctor_set(x_211, 9, x_210);
lean_ctor_set(x_25, 0, x_211);
return x_24;
}
else
{
lean_object* x_212; 
lean_dec(x_188);
lean_dec(x_187);
lean_free_object(x_25);
lean_dec(x_180);
lean_dec(x_23);
lean_dec(x_22);
x_212 = lean_box(0);
lean_ctor_set(x_24, 0, x_212);
return x_24;
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_213 = lean_ctor_get(x_25, 0);
lean_inc(x_213);
lean_dec(x_25);
x_214 = lean_box(0);
x_215 = l_Lean_Expr_sort___override(x_214);
x_216 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_216);
x_217 = lean_mk_array(x_216, x_215);
x_218 = lean_unsigned_to_nat(1u);
x_219 = lean_nat_sub(x_216, x_218);
lean_dec(x_216);
x_220 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_217, x_219);
x_221 = lean_array_get_size(x_220);
x_222 = l_Lean_Meta_Match_MatcherInfo_arity(x_213);
x_223 = lean_nat_dec_lt(x_221, x_222);
lean_dec(x_222);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_224 = lean_array_mk(x_23);
x_225 = lean_ctor_get(x_213, 3);
lean_inc(x_225);
x_226 = lean_ctor_get(x_213, 4);
lean_inc(x_226);
x_227 = lean_unsigned_to_nat(0u);
x_228 = lean_ctor_get(x_213, 0);
lean_inc(x_228);
lean_inc(x_228);
x_229 = l_Array_extract(lean_box(0), x_220, x_227, x_228);
x_230 = l_Lean_instInhabitedExpr;
x_231 = lean_array_get(x_230, x_220, x_228);
x_232 = lean_nat_add(x_228, x_218);
lean_dec(x_228);
x_233 = lean_ctor_get(x_213, 1);
lean_inc(x_233);
x_234 = lean_nat_add(x_232, x_233);
lean_dec(x_233);
lean_inc(x_234);
lean_inc(x_220);
x_235 = l_Array_toSubarray___redArg(x_220, x_232, x_234);
x_236 = l_Array_ofSubarray___redArg(x_235);
lean_dec(x_235);
x_237 = lean_ctor_get(x_213, 2);
lean_inc(x_237);
x_238 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_213);
lean_dec(x_213);
x_239 = lean_nat_add(x_234, x_238);
lean_dec(x_238);
lean_inc(x_239);
lean_inc(x_220);
x_240 = l_Array_toSubarray___redArg(x_220, x_234, x_239);
x_241 = l_Array_ofSubarray___redArg(x_240);
lean_dec(x_240);
x_242 = l_Array_toSubarray___redArg(x_220, x_239, x_221);
x_243 = l_Array_ofSubarray___redArg(x_242);
lean_dec(x_242);
x_244 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_244, 0, x_22);
lean_ctor_set(x_244, 1, x_224);
lean_ctor_set(x_244, 2, x_225);
lean_ctor_set(x_244, 3, x_226);
lean_ctor_set(x_244, 4, x_229);
lean_ctor_set(x_244, 5, x_231);
lean_ctor_set(x_244, 6, x_236);
lean_ctor_set(x_244, 7, x_237);
lean_ctor_set(x_244, 8, x_241);
lean_ctor_set(x_244, 9, x_243);
x_245 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_24, 0, x_245);
return x_24;
}
else
{
lean_object* x_246; 
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_213);
lean_dec(x_23);
lean_dec(x_22);
x_246 = lean_box(0);
lean_ctor_set(x_24, 0, x_246);
return x_24;
}
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; 
x_247 = lean_ctor_get(x_24, 1);
lean_inc(x_247);
lean_dec(x_24);
x_248 = lean_ctor_get(x_25, 0);
lean_inc(x_248);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_249 = x_25;
} else {
 lean_dec_ref(x_25);
 x_249 = lean_box(0);
}
x_250 = lean_box(0);
x_251 = l_Lean_Expr_sort___override(x_250);
x_252 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_252);
x_253 = lean_mk_array(x_252, x_251);
x_254 = lean_unsigned_to_nat(1u);
x_255 = lean_nat_sub(x_252, x_254);
lean_dec(x_252);
x_256 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_253, x_255);
x_257 = lean_array_get_size(x_256);
x_258 = l_Lean_Meta_Match_MatcherInfo_arity(x_248);
x_259 = lean_nat_dec_lt(x_257, x_258);
lean_dec(x_258);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_260 = lean_array_mk(x_23);
x_261 = lean_ctor_get(x_248, 3);
lean_inc(x_261);
x_262 = lean_ctor_get(x_248, 4);
lean_inc(x_262);
x_263 = lean_unsigned_to_nat(0u);
x_264 = lean_ctor_get(x_248, 0);
lean_inc(x_264);
lean_inc(x_264);
x_265 = l_Array_extract(lean_box(0), x_256, x_263, x_264);
x_266 = l_Lean_instInhabitedExpr;
x_267 = lean_array_get(x_266, x_256, x_264);
x_268 = lean_nat_add(x_264, x_254);
lean_dec(x_264);
x_269 = lean_ctor_get(x_248, 1);
lean_inc(x_269);
x_270 = lean_nat_add(x_268, x_269);
lean_dec(x_269);
lean_inc(x_270);
lean_inc(x_256);
x_271 = l_Array_toSubarray___redArg(x_256, x_268, x_270);
x_272 = l_Array_ofSubarray___redArg(x_271);
lean_dec(x_271);
x_273 = lean_ctor_get(x_248, 2);
lean_inc(x_273);
x_274 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_248);
lean_dec(x_248);
x_275 = lean_nat_add(x_270, x_274);
lean_dec(x_274);
lean_inc(x_275);
lean_inc(x_256);
x_276 = l_Array_toSubarray___redArg(x_256, x_270, x_275);
x_277 = l_Array_ofSubarray___redArg(x_276);
lean_dec(x_276);
x_278 = l_Array_toSubarray___redArg(x_256, x_275, x_257);
x_279 = l_Array_ofSubarray___redArg(x_278);
lean_dec(x_278);
x_280 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_280, 0, x_22);
lean_ctor_set(x_280, 1, x_260);
lean_ctor_set(x_280, 2, x_261);
lean_ctor_set(x_280, 3, x_262);
lean_ctor_set(x_280, 4, x_265);
lean_ctor_set(x_280, 5, x_267);
lean_ctor_set(x_280, 6, x_272);
lean_ctor_set(x_280, 7, x_273);
lean_ctor_set(x_280, 8, x_277);
lean_ctor_set(x_280, 9, x_279);
if (lean_is_scalar(x_249)) {
 x_281 = lean_alloc_ctor(1, 1, 0);
} else {
 x_281 = x_249;
}
lean_ctor_set(x_281, 0, x_280);
x_282 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_247);
return x_282;
}
else
{
lean_object* x_283; lean_object* x_284; 
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_23);
lean_dec(x_22);
x_283 = lean_box(0);
x_284 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_247);
return x_284;
}
}
}
}
case 5:
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_1);
x_285 = lean_ctor_get(x_9, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_9, 1);
lean_inc(x_286);
lean_dec(x_9);
x_287 = l_Lean_Expr_app___override(x_285, x_286);
x_288 = l_Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3___lam__1(x_8, x_287, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_287);
return x_288;
}
case 6:
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_1);
x_289 = lean_ctor_get(x_9, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_9, 1);
lean_inc(x_290);
x_291 = lean_ctor_get(x_9, 2);
lean_inc(x_291);
x_292 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 8);
lean_dec(x_9);
x_293 = l_Lean_Expr_lam___override(x_289, x_290, x_291, x_292);
x_294 = l_Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3___lam__1(x_8, x_293, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_293);
return x_294;
}
case 7:
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; uint8_t x_298; lean_object* x_299; lean_object* x_300; 
lean_dec(x_1);
x_295 = lean_ctor_get(x_9, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_9, 1);
lean_inc(x_296);
x_297 = lean_ctor_get(x_9, 2);
lean_inc(x_297);
x_298 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 8);
lean_dec(x_9);
x_299 = l_Lean_Expr_forallE___override(x_295, x_296, x_297, x_298);
x_300 = l_Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3___lam__1(x_8, x_299, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_299);
return x_300;
}
case 8:
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; lean_object* x_306; lean_object* x_307; 
lean_dec(x_1);
x_301 = lean_ctor_get(x_9, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_9, 1);
lean_inc(x_302);
x_303 = lean_ctor_get(x_9, 2);
lean_inc(x_303);
x_304 = lean_ctor_get(x_9, 3);
lean_inc(x_304);
x_305 = lean_ctor_get_uint8(x_9, sizeof(void*)*4 + 8);
lean_dec(x_9);
x_306 = l_Lean_Expr_letE___override(x_301, x_302, x_303, x_304, x_305);
x_307 = l_Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3___lam__1(x_8, x_306, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_306);
return x_307;
}
case 9:
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_dec(x_1);
x_308 = lean_ctor_get(x_9, 0);
lean_inc(x_308);
lean_dec(x_9);
x_309 = l_Lean_Expr_lit___override(x_308);
x_310 = l_Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3___lam__1(x_8, x_309, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_309);
return x_310;
}
case 10:
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_1);
x_311 = lean_ctor_get(x_9, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_9, 1);
lean_inc(x_312);
lean_dec(x_9);
x_313 = l_Lean_Expr_mdata___override(x_311, x_312);
x_314 = l_Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3___lam__1(x_8, x_313, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_313);
return x_314;
}
default: 
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
lean_dec(x_1);
x_315 = lean_ctor_get(x_9, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_9, 1);
lean_inc(x_316);
x_317 = lean_ctor_get(x_9, 2);
lean_inc(x_317);
lean_dec(x_9);
x_318 = l_Lean_Expr_proj___override(x_315, x_316, x_317);
x_319 = l_Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3___lam__1(x_8, x_318, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_318);
return x_319;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__7___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__7___redArg___lam__0), 8, 1);
lean_closure_set(x_10, 0, x_3);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_2);
x_13 = lean_unbox(x_11);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___redArg(x_1, x_13, x_12, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_12);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_lambdaBoundedTelescope___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__7___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__8___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_smartUnfoldingMatch_x3f(x_3);
if (lean_obj_tag(x_4) == 0)
{
return x_1;
}
else
{
lean_dec(x_4);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__8___lam__1(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_26; lean_object* x_33; uint8_t x_34; 
x_33 = lean_array_get_size(x_9);
x_34 = lean_nat_dec_eq(x_33, x_6);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
x_35 = lean_mk_string_unchecked("unexpected matcher application alternative", 42, 42);
x_36 = l_Lean_stringToMessageData(x_35);
lean_dec(x_35);
x_37 = l_Lean_indentExpr(x_7);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_mk_string_unchecked("\nat application", 15, 15);
x_40 = l_Lean_stringToMessageData(x_39);
lean_dec(x_39);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_indentExpr(x_8);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_mk_string_unchecked("", 0, 0);
x_45 = l_Lean_stringToMessageData(x_44);
lean_dec(x_44);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_46, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
return x_47;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_47);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
x_26 = x_15;
goto block_32;
}
block_25:
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_box(1);
x_23 = lean_unbox(x_22);
x_24 = l_Lean_Meta_mkLambdaFVars(x_9, x_21, x_1, x_2, x_1, x_23, x_19, x_18, x_16, x_17, x_20);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_18);
lean_dec(x_19);
return x_24;
}
block_32:
{
lean_object* x_27; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_27 = l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit(x_3, x_4, x_10, x_11, x_12, x_13, x_14, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_find_expr(x_5, x_28);
if (lean_obj_tag(x_30) == 0)
{
if (x_2 == 0)
{
x_16 = x_13;
x_17 = x_14;
x_18 = x_12;
x_19 = x_11;
x_20 = x_29;
x_21 = x_28;
goto block_25;
}
else
{
lean_object* x_31; 
x_31 = l_Lean_Meta_markSmartUnfoldingMatchAlt(x_28);
x_16 = x_13;
x_17 = x_14;
x_18 = x_12;
x_19 = x_11;
x_20 = x_29;
x_21 = x_31;
goto block_25;
}
}
else
{
lean_dec(x_30);
x_16 = x_13;
x_17 = x_14;
x_18 = x_12;
x_19 = x_11;
x_20 = x_29;
x_21 = x_28;
goto block_25;
}
}
else
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_6, x_5);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 2);
lean_inc(x_18);
x_19 = lean_nat_dec_lt(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_16);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_12);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_1, 3);
lean_inc(x_22);
x_23 = lean_box(0);
lean_inc(x_2);
x_24 = l_Lean_Elab_Structural_recArgHasLooseBVarsAt(x_22, x_2, x_3);
x_25 = lean_box(x_24);
x_26 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__8___lam__0___boxed), 3, 2);
lean_closure_set(x_26, 0, x_23);
lean_closure_set(x_26, 1, x_25);
x_27 = lean_array_uget(x_4, x_6);
x_28 = lean_ctor_get(x_15, 0);
lean_inc(x_28);
lean_dec(x_15);
x_29 = lean_array_fget(x_28, x_17);
x_30 = lean_box(x_24);
lean_inc(x_3);
lean_inc(x_27);
lean_inc(x_29);
lean_inc(x_2);
lean_inc(x_1);
x_31 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__8___lam__1___boxed), 15, 8);
lean_closure_set(x_31, 0, x_23);
lean_closure_set(x_31, 1, x_30);
lean_closure_set(x_31, 2, x_1);
lean_closure_set(x_31, 3, x_2);
lean_closure_set(x_31, 4, x_26);
lean_closure_set(x_31, 5, x_29);
lean_closure_set(x_31, 6, x_27);
lean_closure_set(x_31, 7, x_3);
x_32 = lean_unbox(x_23);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_33 = l_Lean_Meta_lambdaBoundedTelescope___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__7___redArg(x_27, x_29, x_31, x_32, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; size_t x_41; size_t x_42; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_17, x_36);
lean_dec(x_17);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_28);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_18);
x_39 = lean_array_push(x_16, x_34);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_usize_of_nat(x_36);
x_42 = lean_usize_add(x_6, x_41);
x_6 = x_42;
x_7 = x_40;
x_12 = x_35;
goto _start;
}
else
{
uint8_t x_44; 
lean_dec(x_28);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_33);
if (x_44 == 0)
{
return x_33;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_33, 0);
x_46 = lean_ctor_get(x_33, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_33);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__9___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__9___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__9___redArg___lam__0), 7, 1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_withLetDecl___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__9___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = lean_box(1);
x_15 = lean_box(1);
x_16 = lean_unbox(x_13);
x_17 = lean_unbox(x_14);
x_18 = lean_unbox(x_13);
x_19 = lean_unbox(x_15);
x_20 = l_Lean_Meta_mkLambdaFVars(x_3, x_11, x_16, x_17, x_18, x_19, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_20;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = lean_box(1);
x_15 = lean_box(1);
x_16 = lean_unbox(x_13);
x_17 = lean_unbox(x_14);
x_18 = lean_unbox(x_15);
x_19 = l_Lean_Meta_mkForallFVars(x_3, x_11, x_16, x_17, x_18, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_19;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_expr_instantiate1(x_1, x_4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_11 = l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit(x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_array_push(x_15, x_4);
x_17 = lean_box(1);
x_18 = lean_box(1);
x_19 = lean_unbox(x_17);
x_20 = lean_unbox(x_18);
x_21 = l_Lean_Meta_mkLetFVars(x_16, x_12, x_19, x_20, x_5, x_6, x_7, x_8, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_16);
return x_21;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 5:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = l_Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3(x_3, x_10, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
x_14 = x_3;
x_15 = x_4;
x_16 = x_5;
x_17 = x_6;
x_18 = x_7;
goto block_26;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_12, 0);
lean_inc(x_27);
lean_dec(x_12);
x_28 = lean_ctor_get(x_1, 3);
lean_inc(x_28);
lean_inc(x_2);
x_29 = l_Lean_Elab_Structural_recArgHasLooseBVarsAt(x_28, x_2, x_3);
if (x_29 == 0)
{
lean_dec(x_27);
x_14 = x_3;
x_15 = x_4;
x_16 = x_5;
x_17 = x_6;
x_18 = x_7;
goto block_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; lean_object* x_39; 
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_mk_empty_array_with_capacity(x_30);
x_32 = lean_ctor_get(x_27, 7);
lean_inc(x_32);
x_33 = lean_array_get_size(x_32);
lean_inc(x_32);
x_34 = l_Array_toSubarray___redArg(x_32, x_30, x_33);
x_35 = lean_ctor_get(x_27, 8);
lean_inc(x_35);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_31);
x_37 = lean_array_size(x_35);
x_38 = lean_usize_of_nat(x_30);
x_39 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__8(x_1, x_2, x_3, x_35, x_37, x_38, x_36, x_4, x_5, x_6, x_7, x_13);
lean_dec(x_35);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_ctor_get(x_27, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_27, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_27, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_27, 3);
lean_inc(x_46);
x_47 = lean_ctor_get(x_27, 4);
lean_inc(x_47);
x_48 = lean_ctor_get(x_27, 5);
lean_inc(x_48);
x_49 = lean_ctor_get(x_27, 6);
lean_inc(x_49);
x_50 = lean_ctor_get(x_27, 9);
lean_inc(x_50);
lean_dec(x_27);
x_51 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_51, 0, x_43);
lean_ctor_set(x_51, 1, x_44);
lean_ctor_set(x_51, 2, x_45);
lean_ctor_set(x_51, 3, x_46);
lean_ctor_set(x_51, 4, x_47);
lean_ctor_set(x_51, 5, x_48);
lean_ctor_set(x_51, 6, x_49);
lean_ctor_set(x_51, 7, x_32);
lean_ctor_set(x_51, 8, x_42);
lean_ctor_set(x_51, 9, x_50);
x_52 = l_Lean_Meta_MatcherApp_toExpr(x_51);
x_53 = l_Lean_Meta_markSmartUnfoldingMatch(x_52);
lean_ctor_set(x_39, 0, x_53);
return x_39;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_54 = lean_ctor_get(x_39, 0);
x_55 = lean_ctor_get(x_39, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_39);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_ctor_get(x_27, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_27, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_27, 2);
lean_inc(x_59);
x_60 = lean_ctor_get(x_27, 3);
lean_inc(x_60);
x_61 = lean_ctor_get(x_27, 4);
lean_inc(x_61);
x_62 = lean_ctor_get(x_27, 5);
lean_inc(x_62);
x_63 = lean_ctor_get(x_27, 6);
lean_inc(x_63);
x_64 = lean_ctor_get(x_27, 9);
lean_inc(x_64);
lean_dec(x_27);
x_65 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_65, 0, x_57);
lean_ctor_set(x_65, 1, x_58);
lean_ctor_set(x_65, 2, x_59);
lean_ctor_set(x_65, 3, x_60);
lean_ctor_set(x_65, 4, x_61);
lean_ctor_set(x_65, 5, x_62);
lean_ctor_set(x_65, 6, x_63);
lean_ctor_set(x_65, 7, x_32);
lean_ctor_set(x_65, 8, x_56);
lean_ctor_set(x_65, 9, x_64);
x_66 = l_Lean_Meta_MatcherApp_toExpr(x_65);
x_67 = l_Lean_Meta_markSmartUnfoldingMatch(x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_55);
return x_68;
}
}
else
{
uint8_t x_69; 
lean_dec(x_32);
lean_dec(x_27);
x_69 = !lean_is_exclusive(x_39);
if (x_69 == 0)
{
return x_39;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_39, 0);
x_71 = lean_ctor_get(x_39, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_39);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
block_26:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_box(0);
x_20 = l_Lean_Expr_sort___override(x_19);
x_21 = l_Lean_Expr_getAppNumArgs(x_14);
lean_inc(x_21);
x_22 = lean_mk_array(x_21, x_20);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_sub(x_21, x_23);
lean_dec(x_21);
x_25 = l_Lean_Expr_withAppAux___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__1(x_1, x_2, x_14, x_22, x_24, x_15, x_16, x_17, x_18, x_13);
lean_dec(x_24);
return x_25;
}
}
else
{
uint8_t x_73; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_11);
if (x_73 == 0)
{
return x_11;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_11, 0);
x_75 = lean_ctor_get(x_11, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_11);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
case 6:
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; 
x_77 = lean_alloc_closure((void*)(l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___lam__0___boxed), 9, 2);
lean_closure_set(x_77, 0, x_1);
lean_closure_set(x_77, 1, x_2);
x_78 = lean_box(0);
x_79 = lean_unbox(x_78);
x_80 = l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(x_3, x_77, x_79, x_4, x_5, x_6, x_7, x_8);
return x_80;
}
case 7:
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; 
x_81 = lean_alloc_closure((void*)(l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___lam__1___boxed), 9, 2);
lean_closure_set(x_81, 0, x_1);
lean_closure_set(x_81, 1, x_2);
x_82 = lean_box(0);
x_83 = lean_unbox(x_82);
x_84 = l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0(lean_box(0), x_3, x_81, x_83, x_4, x_5, x_6, x_7, x_8);
return x_84;
}
case 8:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_3, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_3, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_3, 2);
lean_inc(x_87);
x_88 = lean_ctor_get(x_3, 3);
lean_inc(x_88);
lean_dec(x_3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_89 = l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit(x_1, x_2, x_87, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_alloc_closure((void*)(l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___lam__2___boxed), 9, 3);
lean_closure_set(x_92, 0, x_88);
lean_closure_set(x_92, 1, x_1);
lean_closure_set(x_92, 2, x_2);
x_93 = lean_box(0);
x_94 = lean_unbox(x_93);
x_95 = l_Lean_Meta_withLetDecl___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__9___redArg(x_85, x_86, x_90, x_92, x_94, x_4, x_5, x_6, x_7, x_91);
return x_95;
}
else
{
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_89;
}
}
case 10:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_3, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_3, 1);
lean_inc(x_97);
lean_dec(x_3);
x_98 = l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit(x_1, x_2, x_97, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_98) == 0)
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_98, 0);
x_101 = l_Lean_Expr_mdata___override(x_96, x_100);
lean_ctor_set(x_98, 0, x_101);
return x_98;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_98, 0);
x_103 = lean_ctor_get(x_98, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_98);
x_104 = l_Lean_Expr_mdata___override(x_96, x_102);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
else
{
lean_dec(x_96);
return x_98;
}
}
case 11:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = lean_ctor_get(x_3, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_3, 1);
lean_inc(x_107);
x_108 = lean_ctor_get(x_3, 2);
lean_inc(x_108);
lean_dec(x_3);
x_109 = l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit(x_1, x_2, x_108, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_109) == 0)
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_109, 0);
x_112 = l_Lean_Expr_proj___override(x_106, x_107, x_111);
lean_ctor_set(x_109, 0, x_112);
return x_109;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_109, 0);
x_114 = lean_ctor_get(x_109, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_109);
x_115 = l_Lean_Expr_proj___override(x_106, x_107, x_113);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
else
{
lean_dec(x_107);
lean_dec(x_106);
return x_109;
}
}
default: 
{
lean_object* x_117; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_3);
lean_ctor_set(x_117, 1, x_8);
return x_117;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_mapMUnsafe_map___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__0(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Expr_withAppAux___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3_spec__4_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_matchMatcherApp_x3f___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__3(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Meta_lambdaBoundedTelescope___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__7___redArg(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l_Lean_Meta_lambdaBoundedTelescope___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__7(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__8___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__8___lam__0(x_4, x_5, x_3);
lean_dec(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__8___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_1);
lean_dec(x_1);
x_17 = lean_unbox(x_2);
lean_dec(x_2);
x_18 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__8___lam__1(x_16, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__8(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l_Lean_Meta_withLetDecl___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__9___redArg(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_6);
lean_dec(x_6);
x_13 = l_Lean_Meta_withLetDecl___at___Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_spec__9(x_1, x_2, x_3, x_4, x_5, x_12, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 5);
lean_inc(x_8);
lean_inc(x_1);
x_9 = l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit(x_1, x_2, x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_box(0);
x_16 = lean_box(0);
x_17 = lean_box(0);
x_18 = lean_box(0);
x_19 = lean_box(0);
x_20 = l_Array_empty(lean_box(0));
x_21 = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_16);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_unbox(x_17);
lean_ctor_set_uint8(x_21, sizeof(void*)*3, x_22);
x_23 = lean_unbox(x_18);
lean_ctor_set_uint8(x_21, sizeof(void*)*3 + 1, x_23);
x_24 = lean_unbox(x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*3 + 2, x_24);
x_25 = lean_unbox(x_18);
lean_ctor_set_uint8(x_21, sizeof(void*)*3 + 3, x_25);
x_26 = lean_ctor_get(x_1, 3);
lean_inc(x_26);
x_27 = lean_mk_string_unchecked("_sunfold", 8, 8);
x_28 = l_Lean_Name_str___override(x_26, x_27);
x_29 = lean_ctor_get(x_1, 4);
lean_inc(x_29);
x_30 = lean_ctor_get(x_1, 6);
lean_inc(x_30);
lean_dec(x_1);
x_31 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_31, 0, x_12);
lean_ctor_set(x_31, 1, x_14);
lean_ctor_set(x_31, 2, x_21);
lean_ctor_set(x_31, 3, x_28);
lean_ctor_set(x_31, 4, x_29);
lean_ctor_set(x_31, 5, x_11);
lean_ctor_set(x_31, 6, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*7, x_13);
lean_ctor_set(x_9, 0, x_31);
return x_9;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_32 = lean_ctor_get(x_9, 0);
x_33 = lean_ctor_get(x_9, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_9);
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
x_35 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
x_37 = lean_box(0);
x_38 = lean_box(0);
x_39 = lean_box(0);
x_40 = lean_box(0);
x_41 = lean_box(0);
x_42 = l_Array_empty(lean_box(0));
x_43 = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_38);
lean_ctor_set(x_43, 2, x_42);
x_44 = lean_unbox(x_39);
lean_ctor_set_uint8(x_43, sizeof(void*)*3, x_44);
x_45 = lean_unbox(x_40);
lean_ctor_set_uint8(x_43, sizeof(void*)*3 + 1, x_45);
x_46 = lean_unbox(x_41);
lean_ctor_set_uint8(x_43, sizeof(void*)*3 + 2, x_46);
x_47 = lean_unbox(x_40);
lean_ctor_set_uint8(x_43, sizeof(void*)*3 + 3, x_47);
x_48 = lean_ctor_get(x_1, 3);
lean_inc(x_48);
x_49 = lean_mk_string_unchecked("_sunfold", 8, 8);
x_50 = l_Lean_Name_str___override(x_48, x_49);
x_51 = lean_ctor_get(x_1, 4);
lean_inc(x_51);
x_52 = lean_ctor_get(x_1, 6);
lean_inc(x_52);
lean_dec(x_1);
x_53 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_53, 0, x_34);
lean_ctor_set(x_53, 1, x_36);
lean_ctor_set(x_53, 2, x_43);
lean_ctor_set(x_53, 3, x_50);
lean_ctor_set(x_53, 4, x_51);
lean_ctor_set(x_53, 5, x_32);
lean_ctor_set(x_53, 6, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*7, x_35);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_33);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_9);
if (x_55 == 0)
{
return x_9;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_9, 0);
x_57 = lean_ctor_get(x_9, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_9);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDef___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_11 = l_Lean_Elab_Structural_addSmartUnfoldingDefAux(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 3);
lean_inc(x_14);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Elab_addNonRec(x_12, x_3, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_8);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDef(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_11 = l_Lean_Meta_isProp(x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_box(1);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Structural_addSmartUnfoldingDef___lam__0___boxed), 10, 3);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_15);
x_17 = lean_unbox(x_12);
lean_dec(x_12);
x_18 = l_Lean_Elab_withEnableInfoTree___at___Lean_Elab_addAndCompilePartialRec_spec__2___redArg(x_17, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_11, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_11, 0, x_21);
return x_11;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_dec(x_11);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
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
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_11);
if (x_25 == 0)
{
return x_11;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_11, 0);
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_11);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDef___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_Elab_Structural_addSmartUnfoldingDef___lam__0(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* initialize_Lean_Elab_PreDefinition_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Structural_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Match_MatcherApp_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_Structural_SmartUnfolding(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_PreDefinition_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Structural_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatcherApp_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
