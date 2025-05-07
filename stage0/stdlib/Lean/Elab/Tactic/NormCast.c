// Lean compiler output
// Module: Lean.Elab.Tactic.NormCast
// Imports: Lean.Meta.Tactic.NormCast Lean.Elab.Tactic.Conv.Simp Lean.Elab.ElabRules
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
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1(lean_object*);
lean_object* l_Lean_Meta_Simp_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(lean_object*);
lean_object* l_Lean_Meta_getCoeFnInfo_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_upwardAndElim___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_elabConfig(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabNormCastConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Elab_Tactic_expandOptLocation(lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_expandLocation(lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_upwardAndElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Meta_Simp_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_x3f(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1(lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftCoreM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastTarget___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
lean_object* l_Lean_Meta_SimpExtension_getTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Context_setFailIfUnchanged(lean_object*, uint8_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_MVarId_getNondepPropHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_findLocalDeclWithType_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_realizeGlobalConstNoOverload(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_mkCoe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_getLhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_NormCast_addElim(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalUnsafe____x40_Lean_Elab_Tactic_NormCast___hyg_6395_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastHyp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_numeralToCoe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_mkCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigItemViews(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_upwardAndElim___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_NormCast_pushCastExt;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastHyp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_simpLocation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkSimpContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1(lean_object*);
lean_object* lean_usize_to_nat(size_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_NormCast_normCastExt;
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1(lean_object*);
lean_object* l_Lean_exceptOptionEmoji___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwTypeMismatchError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_applySimpResultToLocalDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastHyp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_coerce_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastHyp___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg____x40_Lean_Elab_Tactic_NormCast___hyg_6395_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_mkCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_SimprocsArray_add(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNumeral(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___boxed(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__7(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpExtension_getTheorems___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_mkDefaultMethods(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_withTraceNode___at___Lean_Meta_processPostponed_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_upwardAndElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* l_Lean_Meta_evalExpr_x27(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_applySimpResultToTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_applySimpResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastTarget___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalUnsafe____x40_Lean_Elab_Tactic_NormCast___hyg_6395____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostpone(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_2 = lean_mk_string_unchecked("Tactic", 6, 6);
x_3 = lean_mk_string_unchecked("norm_cast", 9, 9);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(0);
x_6 = lean_box(0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_7);
x_8 = l_Lean_Name_str___override(x_6, x_7);
x_9 = lean_mk_string_unchecked("Elab", 4, 4);
lean_inc(x_9);
x_10 = l_Lean_Name_str___override(x_8, x_9);
lean_inc(x_2);
x_11 = l_Lean_Name_str___override(x_10, x_2);
x_12 = lean_mk_string_unchecked("NormCast", 8, 8);
lean_inc(x_12);
x_13 = l_Lean_Name_str___override(x_11, x_12);
x_14 = lean_mk_string_unchecked("initFn", 6, 6);
x_15 = l_Lean_Name_str___override(x_13, x_14);
x_16 = lean_mk_string_unchecked("_@", 2, 2);
x_17 = l_Lean_Name_str___override(x_15, x_16);
x_18 = l_Lean_Name_str___override(x_17, x_7);
x_19 = l_Lean_Name_str___override(x_18, x_9);
x_20 = l_Lean_Name_str___override(x_19, x_2);
x_21 = l_Lean_Name_str___override(x_20, x_12);
x_22 = lean_mk_string_unchecked("_hyg", 4, 4);
x_23 = l_Lean_Name_str___override(x_21, x_22);
x_24 = lean_unsigned_to_nat(5u);
x_25 = l_Lean_Name_num___override(x_23, x_24);
x_26 = lean_unbox(x_5);
x_27 = l_Lean_registerTraceClass(x_4, x_26, x_25, x_1);
return x_27;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsing(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint64_t x_10; lean_object* x_11; uint64_t x_12; uint64_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint64_t x_35; uint8_t x_36; uint64_t x_37; lean_object* x_38; uint8_t x_39; uint64_t x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get_uint64(x_4, sizeof(void*)*7);
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_uint64_of_nat(x_11);
x_13 = lean_uint64_shift_right(x_10, x_12);
x_14 = l_Lean_Meta_getSimpCongrTheorems(x_6, x_7, x_8);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(2);
x_18 = lean_ctor_get_uint8(x_9, 0);
x_19 = lean_ctor_get_uint8(x_9, 1);
x_20 = lean_ctor_get_uint8(x_9, 2);
x_21 = lean_ctor_get_uint8(x_9, 3);
x_22 = lean_ctor_get_uint8(x_9, 4);
x_23 = lean_ctor_get_uint8(x_9, 5);
x_24 = lean_ctor_get_uint8(x_9, 6);
x_25 = lean_ctor_get_uint8(x_9, 7);
x_26 = lean_ctor_get_uint8(x_9, 8);
x_27 = lean_ctor_get_uint8(x_9, 10);
x_28 = lean_ctor_get_uint8(x_9, 11);
x_29 = lean_ctor_get_uint8(x_9, 12);
x_30 = lean_ctor_get_uint8(x_9, 13);
x_31 = lean_ctor_get_uint8(x_9, 14);
x_32 = lean_ctor_get_uint8(x_9, 15);
x_33 = lean_ctor_get_uint8(x_9, 16);
x_34 = lean_ctor_get_uint8(x_9, 17);
x_35 = lean_uint64_shift_left(x_13, x_12);
x_36 = lean_unbox(x_17);
x_37 = l_Lean_Meta_TransparencyMode_toUInt64(x_36);
x_38 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_38, 0, x_18);
lean_ctor_set_uint8(x_38, 1, x_19);
lean_ctor_set_uint8(x_38, 2, x_20);
lean_ctor_set_uint8(x_38, 3, x_21);
lean_ctor_set_uint8(x_38, 4, x_22);
lean_ctor_set_uint8(x_38, 5, x_23);
lean_ctor_set_uint8(x_38, 6, x_24);
lean_ctor_set_uint8(x_38, 7, x_25);
lean_ctor_set_uint8(x_38, 8, x_26);
x_39 = lean_unbox(x_17);
lean_ctor_set_uint8(x_38, 9, x_39);
lean_ctor_set_uint8(x_38, 10, x_27);
lean_ctor_set_uint8(x_38, 11, x_28);
lean_ctor_set_uint8(x_38, 12, x_29);
lean_ctor_set_uint8(x_38, 13, x_30);
lean_ctor_set_uint8(x_38, 14, x_31);
lean_ctor_set_uint8(x_38, 15, x_32);
lean_ctor_set_uint8(x_38, 16, x_33);
lean_ctor_set_uint8(x_38, 17, x_34);
x_40 = lean_uint64_lor(x_35, x_37);
x_41 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 8);
x_42 = lean_ctor_get(x_4, 1);
x_43 = lean_ctor_get(x_4, 2);
x_44 = lean_ctor_get(x_4, 3);
x_45 = lean_ctor_get(x_4, 4);
x_46 = lean_ctor_get(x_4, 5);
x_47 = lean_ctor_get(x_4, 6);
x_48 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 9);
x_49 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 10);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
x_50 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_50, 0, x_38);
lean_ctor_set(x_50, 1, x_42);
lean_ctor_set(x_50, 2, x_43);
lean_ctor_set(x_50, 3, x_44);
lean_ctor_set(x_50, 4, x_45);
lean_ctor_set(x_50, 5, x_46);
lean_ctor_set(x_50, 6, x_47);
lean_ctor_set_uint64(x_50, sizeof(void*)*7, x_40);
lean_ctor_set_uint8(x_50, sizeof(void*)*7 + 8, x_41);
lean_ctor_set_uint8(x_50, sizeof(void*)*7 + 9, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*7 + 10, x_49);
x_51 = lean_unsigned_to_nat(100000u);
x_52 = lean_box(0);
x_53 = lean_box(1);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 20);
lean_ctor_set(x_55, 0, x_51);
lean_ctor_set(x_55, 1, x_11);
x_56 = lean_unbox(x_52);
lean_ctor_set_uint8(x_55, sizeof(void*)*2, x_56);
x_57 = lean_unbox(x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 1, x_57);
x_58 = lean_unbox(x_52);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 2, x_58);
x_59 = lean_unbox(x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 3, x_59);
x_60 = lean_unbox(x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 4, x_60);
x_61 = lean_unbox(x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 5, x_61);
x_62 = lean_unbox(x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 6, x_62);
x_63 = lean_unbox(x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 7, x_63);
x_64 = lean_unbox(x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 8, x_64);
x_65 = lean_unbox(x_52);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 9, x_65);
x_66 = lean_unbox(x_52);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 10, x_66);
x_67 = lean_unbox(x_52);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 11, x_67);
x_68 = lean_unbox(x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 12, x_68);
x_69 = lean_unbox(x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 13, x_69);
x_70 = lean_unbox(x_52);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 14, x_70);
x_71 = lean_unbox(x_52);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 15, x_71);
x_72 = lean_unbox(x_52);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 16, x_72);
x_73 = lean_unbox(x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 17, x_73);
x_74 = lean_unbox(x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 18, x_74);
x_75 = lean_unbox(x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 19, x_75);
x_76 = lean_unsigned_to_nat(1u);
x_77 = lean_mk_empty_array_with_capacity(x_76);
x_78 = lean_array_push(x_77, x_1);
x_79 = l_Lean_Meta_Simp_mkContext(x_55, x_78, x_15, x_50, x_5, x_6, x_7, x_16);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_81 = lean_ctor_get(x_79, 0);
x_82 = lean_ctor_get(x_79, 1);
x_83 = l_Lean_Meta_Simp_mkDefaultMethods(x_6, x_7, x_82);
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; size_t x_102; lean_object* x_103; lean_object* x_104; size_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_123; 
x_85 = lean_ctor_get(x_83, 0);
x_86 = lean_ctor_get(x_83, 1);
x_87 = lean_unsigned_to_nat(8u);
x_88 = lean_unsigned_to_nat(0u);
x_89 = lean_nat_shiftl(x_87, x_11);
x_90 = lean_unsigned_to_nat(3u);
x_91 = lean_nat_div(x_89, x_90);
lean_dec(x_89);
x_92 = l_Nat_nextPowerOfTwo(x_91);
lean_dec(x_91);
x_93 = lean_box(0);
x_94 = lean_mk_array(x_92, x_93);
lean_ctor_set(x_83, 1, x_94);
lean_ctor_set(x_83, 0, x_88);
x_95 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_95);
x_96 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_96, 0, x_95);
lean_inc(x_83);
x_97 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_97, 0, x_83);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_unbox(x_53);
lean_ctor_set_uint8(x_97, sizeof(void*)*2, x_98);
lean_inc(x_95);
x_99 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_99, 0, x_95);
lean_inc(x_99);
lean_ctor_set(x_79, 1, x_88);
lean_ctor_set(x_79, 0, x_99);
x_100 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_100, 0, x_95);
x_101 = lean_unsigned_to_nat(5u);
x_102 = lean_usize_of_nat(x_101);
x_103 = lean_usize_to_nat(x_102);
x_104 = lean_nat_pow(x_11, x_103);
lean_dec(x_103);
x_105 = lean_usize_of_nat(x_104);
lean_dec(x_104);
x_106 = lean_usize_to_nat(x_105);
x_107 = lean_mk_empty_array_with_capacity(x_106);
lean_dec(x_106);
lean_inc(x_107);
x_108 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_108, 0, x_107);
x_109 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_107);
lean_ctor_set(x_109, 2, x_88);
lean_ctor_set(x_109, 3, x_88);
lean_ctor_set_usize(x_109, 4, x_102);
lean_inc(x_99);
x_110 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_110, 0, x_99);
lean_ctor_set(x_110, 1, x_99);
lean_ctor_set(x_110, 2, x_100);
lean_ctor_set(x_110, 3, x_109);
x_111 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_111, 0, x_97);
lean_ctor_set(x_111, 1, x_83);
lean_ctor_set(x_111, 2, x_79);
lean_ctor_set(x_111, 3, x_88);
lean_ctor_set(x_111, 4, x_110);
x_112 = lean_st_mk_ref(x_111, x_86);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_50);
lean_inc(x_113);
lean_inc(x_81);
lean_inc(x_85);
x_123 = lean_simp(x_2, x_85, x_81, x_113, x_50, x_5, x_6, x_7, x_114);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_50);
lean_inc(x_113);
lean_inc(x_3);
x_126 = lean_simp(x_3, x_85, x_81, x_113, x_50, x_5, x_6, x_7, x_125);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_ctor_get(x_124, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_127, 0);
lean_inc(x_130);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_131 = l_Lean_Meta_isExprDefEq(x_129, x_130, x_50, x_5, x_6, x_7, x_128);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; uint8_t x_133; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_unbox(x_132);
lean_dec(x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_127);
lean_dec(x_124);
lean_dec(x_50);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
lean_dec(x_131);
x_135 = lean_box(0);
x_115 = x_135;
x_116 = x_134;
goto block_122;
}
else
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_131, 1);
lean_inc(x_136);
lean_dec(x_131);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_50);
x_137 = l_Lean_Meta_Simp_Result_mkEqSymm(x_3, x_127, x_50, x_5, x_6, x_7, x_136);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_140 = l_Lean_Meta_Simp_Result_mkEqTrans(x_124, x_138, x_50, x_5, x_6, x_7, x_139);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_143, 0, x_141);
x_115 = x_143;
x_116 = x_142;
goto block_122;
}
else
{
uint8_t x_144; 
lean_dec(x_113);
x_144 = !lean_is_exclusive(x_140);
if (x_144 == 0)
{
return x_140;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_140, 0);
x_146 = lean_ctor_get(x_140, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_140);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
else
{
uint8_t x_148; 
lean_dec(x_124);
lean_dec(x_113);
lean_dec(x_50);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_148 = !lean_is_exclusive(x_137);
if (x_148 == 0)
{
return x_137;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_137, 0);
x_150 = lean_ctor_get(x_137, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_137);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
}
else
{
uint8_t x_152; 
lean_dec(x_127);
lean_dec(x_124);
lean_dec(x_113);
lean_dec(x_50);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_152 = !lean_is_exclusive(x_131);
if (x_152 == 0)
{
return x_131;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_131, 0);
x_154 = lean_ctor_get(x_131, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_131);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
else
{
uint8_t x_156; 
lean_dec(x_124);
lean_dec(x_113);
lean_dec(x_50);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_156 = !lean_is_exclusive(x_126);
if (x_156 == 0)
{
return x_126;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_126, 0);
x_158 = lean_ctor_get(x_126, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_126);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
else
{
uint8_t x_160; 
lean_dec(x_113);
lean_dec(x_85);
lean_dec(x_81);
lean_dec(x_50);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_160 = !lean_is_exclusive(x_123);
if (x_160 == 0)
{
return x_123;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_123, 0);
x_162 = lean_ctor_get(x_123, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_123);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
}
block_122:
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_st_ref_get(x_113, x_116);
lean_dec(x_113);
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_117, 0);
lean_dec(x_119);
lean_ctor_set(x_117, 0, x_115);
return x_117;
}
else
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_117, 1);
lean_inc(x_120);
lean_dec(x_117);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_115);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; size_t x_182; lean_object* x_183; lean_object* x_184; size_t x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_202; 
x_164 = lean_ctor_get(x_83, 0);
x_165 = lean_ctor_get(x_83, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_83);
x_166 = lean_unsigned_to_nat(8u);
x_167 = lean_unsigned_to_nat(0u);
x_168 = lean_nat_shiftl(x_166, x_11);
x_169 = lean_unsigned_to_nat(3u);
x_170 = lean_nat_div(x_168, x_169);
lean_dec(x_168);
x_171 = l_Nat_nextPowerOfTwo(x_170);
lean_dec(x_170);
x_172 = lean_box(0);
x_173 = lean_mk_array(x_171, x_172);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_167);
lean_ctor_set(x_174, 1, x_173);
x_175 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_175);
x_176 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_176, 0, x_175);
lean_inc(x_174);
x_177 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_176);
x_178 = lean_unbox(x_53);
lean_ctor_set_uint8(x_177, sizeof(void*)*2, x_178);
lean_inc(x_175);
x_179 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_179, 0, x_175);
lean_inc(x_179);
lean_ctor_set(x_79, 1, x_167);
lean_ctor_set(x_79, 0, x_179);
x_180 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_180, 0, x_175);
x_181 = lean_unsigned_to_nat(5u);
x_182 = lean_usize_of_nat(x_181);
x_183 = lean_usize_to_nat(x_182);
x_184 = lean_nat_pow(x_11, x_183);
lean_dec(x_183);
x_185 = lean_usize_of_nat(x_184);
lean_dec(x_184);
x_186 = lean_usize_to_nat(x_185);
x_187 = lean_mk_empty_array_with_capacity(x_186);
lean_dec(x_186);
lean_inc(x_187);
x_188 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_188, 0, x_187);
x_189 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_187);
lean_ctor_set(x_189, 2, x_167);
lean_ctor_set(x_189, 3, x_167);
lean_ctor_set_usize(x_189, 4, x_182);
lean_inc(x_179);
x_190 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_190, 0, x_179);
lean_ctor_set(x_190, 1, x_179);
lean_ctor_set(x_190, 2, x_180);
lean_ctor_set(x_190, 3, x_189);
x_191 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_191, 0, x_177);
lean_ctor_set(x_191, 1, x_174);
lean_ctor_set(x_191, 2, x_79);
lean_ctor_set(x_191, 3, x_167);
lean_ctor_set(x_191, 4, x_190);
x_192 = lean_st_mk_ref(x_191, x_165);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_50);
lean_inc(x_193);
lean_inc(x_81);
lean_inc(x_164);
x_202 = lean_simp(x_2, x_164, x_81, x_193, x_50, x_5, x_6, x_7, x_194);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec(x_202);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_50);
lean_inc(x_193);
lean_inc(x_3);
x_205 = lean_simp(x_3, x_164, x_81, x_193, x_50, x_5, x_6, x_7, x_204);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
lean_dec(x_205);
x_208 = lean_ctor_get(x_203, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_206, 0);
lean_inc(x_209);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_210 = l_Lean_Meta_isExprDefEq(x_208, x_209, x_50, x_5, x_6, x_7, x_207);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; uint8_t x_212; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_unbox(x_211);
lean_dec(x_211);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; 
lean_dec(x_206);
lean_dec(x_203);
lean_dec(x_50);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_213 = lean_ctor_get(x_210, 1);
lean_inc(x_213);
lean_dec(x_210);
x_214 = lean_box(0);
x_195 = x_214;
x_196 = x_213;
goto block_201;
}
else
{
lean_object* x_215; lean_object* x_216; 
x_215 = lean_ctor_get(x_210, 1);
lean_inc(x_215);
lean_dec(x_210);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_50);
x_216 = l_Lean_Meta_Simp_Result_mkEqSymm(x_3, x_206, x_50, x_5, x_6, x_7, x_215);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
lean_dec(x_216);
x_219 = l_Lean_Meta_Simp_Result_mkEqTrans(x_203, x_217, x_50, x_5, x_6, x_7, x_218);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
x_222 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_222, 0, x_220);
x_195 = x_222;
x_196 = x_221;
goto block_201;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_193);
x_223 = lean_ctor_get(x_219, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_219, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_225 = x_219;
} else {
 lean_dec_ref(x_219);
 x_225 = lean_box(0);
}
if (lean_is_scalar(x_225)) {
 x_226 = lean_alloc_ctor(1, 2, 0);
} else {
 x_226 = x_225;
}
lean_ctor_set(x_226, 0, x_223);
lean_ctor_set(x_226, 1, x_224);
return x_226;
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_203);
lean_dec(x_193);
lean_dec(x_50);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_227 = lean_ctor_get(x_216, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_216, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 x_229 = x_216;
} else {
 lean_dec_ref(x_216);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(1, 2, 0);
} else {
 x_230 = x_229;
}
lean_ctor_set(x_230, 0, x_227);
lean_ctor_set(x_230, 1, x_228);
return x_230;
}
}
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_206);
lean_dec(x_203);
lean_dec(x_193);
lean_dec(x_50);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_231 = lean_ctor_get(x_210, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_210, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_233 = x_210;
} else {
 lean_dec_ref(x_210);
 x_233 = lean_box(0);
}
if (lean_is_scalar(x_233)) {
 x_234 = lean_alloc_ctor(1, 2, 0);
} else {
 x_234 = x_233;
}
lean_ctor_set(x_234, 0, x_231);
lean_ctor_set(x_234, 1, x_232);
return x_234;
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
lean_dec(x_203);
lean_dec(x_193);
lean_dec(x_50);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_235 = lean_ctor_get(x_205, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_205, 1);
lean_inc(x_236);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_237 = x_205;
} else {
 lean_dec_ref(x_205);
 x_237 = lean_box(0);
}
if (lean_is_scalar(x_237)) {
 x_238 = lean_alloc_ctor(1, 2, 0);
} else {
 x_238 = x_237;
}
lean_ctor_set(x_238, 0, x_235);
lean_ctor_set(x_238, 1, x_236);
return x_238;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_dec(x_193);
lean_dec(x_164);
lean_dec(x_81);
lean_dec(x_50);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_239 = lean_ctor_get(x_202, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_202, 1);
lean_inc(x_240);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_241 = x_202;
} else {
 lean_dec_ref(x_202);
 x_241 = lean_box(0);
}
if (lean_is_scalar(x_241)) {
 x_242 = lean_alloc_ctor(1, 2, 0);
} else {
 x_242 = x_241;
}
lean_ctor_set(x_242, 0, x_239);
lean_ctor_set(x_242, 1, x_240);
return x_242;
}
block_201:
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_197 = lean_st_ref_get(x_193, x_196);
lean_dec(x_193);
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
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_195);
lean_ctor_set(x_200, 1, x_198);
return x_200;
}
}
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; size_t x_266; lean_object* x_267; lean_object* x_268; size_t x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_286; 
x_243 = lean_ctor_get(x_79, 0);
x_244 = lean_ctor_get(x_79, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_79);
x_245 = l_Lean_Meta_Simp_mkDefaultMethods(x_6, x_7, x_244);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_248 = x_245;
} else {
 lean_dec_ref(x_245);
 x_248 = lean_box(0);
}
x_249 = lean_unsigned_to_nat(8u);
x_250 = lean_unsigned_to_nat(0u);
x_251 = lean_nat_shiftl(x_249, x_11);
x_252 = lean_unsigned_to_nat(3u);
x_253 = lean_nat_div(x_251, x_252);
lean_dec(x_251);
x_254 = l_Nat_nextPowerOfTwo(x_253);
lean_dec(x_253);
x_255 = lean_box(0);
x_256 = lean_mk_array(x_254, x_255);
if (lean_is_scalar(x_248)) {
 x_257 = lean_alloc_ctor(0, 2, 0);
} else {
 x_257 = x_248;
}
lean_ctor_set(x_257, 0, x_250);
lean_ctor_set(x_257, 1, x_256);
x_258 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_258);
x_259 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_259, 0, x_258);
lean_inc(x_257);
x_260 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_260, 0, x_257);
lean_ctor_set(x_260, 1, x_259);
x_261 = lean_unbox(x_53);
lean_ctor_set_uint8(x_260, sizeof(void*)*2, x_261);
lean_inc(x_258);
x_262 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_262, 0, x_258);
lean_inc(x_262);
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_250);
x_264 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_264, 0, x_258);
x_265 = lean_unsigned_to_nat(5u);
x_266 = lean_usize_of_nat(x_265);
x_267 = lean_usize_to_nat(x_266);
x_268 = lean_nat_pow(x_11, x_267);
lean_dec(x_267);
x_269 = lean_usize_of_nat(x_268);
lean_dec(x_268);
x_270 = lean_usize_to_nat(x_269);
x_271 = lean_mk_empty_array_with_capacity(x_270);
lean_dec(x_270);
lean_inc(x_271);
x_272 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_272, 0, x_271);
x_273 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_271);
lean_ctor_set(x_273, 2, x_250);
lean_ctor_set(x_273, 3, x_250);
lean_ctor_set_usize(x_273, 4, x_266);
lean_inc(x_262);
x_274 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_274, 0, x_262);
lean_ctor_set(x_274, 1, x_262);
lean_ctor_set(x_274, 2, x_264);
lean_ctor_set(x_274, 3, x_273);
x_275 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_275, 0, x_260);
lean_ctor_set(x_275, 1, x_257);
lean_ctor_set(x_275, 2, x_263);
lean_ctor_set(x_275, 3, x_250);
lean_ctor_set(x_275, 4, x_274);
x_276 = lean_st_mk_ref(x_275, x_247);
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
lean_dec(x_276);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_50);
lean_inc(x_277);
lean_inc(x_243);
lean_inc(x_246);
x_286 = lean_simp(x_2, x_246, x_243, x_277, x_50, x_5, x_6, x_7, x_278);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec(x_286);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_50);
lean_inc(x_277);
lean_inc(x_3);
x_289 = lean_simp(x_3, x_246, x_243, x_277, x_50, x_5, x_6, x_7, x_288);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_289, 1);
lean_inc(x_291);
lean_dec(x_289);
x_292 = lean_ctor_get(x_287, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_290, 0);
lean_inc(x_293);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_294 = l_Lean_Meta_isExprDefEq(x_292, x_293, x_50, x_5, x_6, x_7, x_291);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; uint8_t x_296; 
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
x_296 = lean_unbox(x_295);
lean_dec(x_295);
if (x_296 == 0)
{
lean_object* x_297; lean_object* x_298; 
lean_dec(x_290);
lean_dec(x_287);
lean_dec(x_50);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_297 = lean_ctor_get(x_294, 1);
lean_inc(x_297);
lean_dec(x_294);
x_298 = lean_box(0);
x_279 = x_298;
x_280 = x_297;
goto block_285;
}
else
{
lean_object* x_299; lean_object* x_300; 
x_299 = lean_ctor_get(x_294, 1);
lean_inc(x_299);
lean_dec(x_294);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_50);
x_300 = l_Lean_Meta_Simp_Result_mkEqSymm(x_3, x_290, x_50, x_5, x_6, x_7, x_299);
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_300, 1);
lean_inc(x_302);
lean_dec(x_300);
x_303 = l_Lean_Meta_Simp_Result_mkEqTrans(x_287, x_301, x_50, x_5, x_6, x_7, x_302);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_303, 1);
lean_inc(x_305);
lean_dec(x_303);
x_306 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_306, 0, x_304);
x_279 = x_306;
x_280 = x_305;
goto block_285;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_dec(x_277);
x_307 = lean_ctor_get(x_303, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_303, 1);
lean_inc(x_308);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 lean_ctor_release(x_303, 1);
 x_309 = x_303;
} else {
 lean_dec_ref(x_303);
 x_309 = lean_box(0);
}
if (lean_is_scalar(x_309)) {
 x_310 = lean_alloc_ctor(1, 2, 0);
} else {
 x_310 = x_309;
}
lean_ctor_set(x_310, 0, x_307);
lean_ctor_set(x_310, 1, x_308);
return x_310;
}
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_287);
lean_dec(x_277);
lean_dec(x_50);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_311 = lean_ctor_get(x_300, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_300, 1);
lean_inc(x_312);
if (lean_is_exclusive(x_300)) {
 lean_ctor_release(x_300, 0);
 lean_ctor_release(x_300, 1);
 x_313 = x_300;
} else {
 lean_dec_ref(x_300);
 x_313 = lean_box(0);
}
if (lean_is_scalar(x_313)) {
 x_314 = lean_alloc_ctor(1, 2, 0);
} else {
 x_314 = x_313;
}
lean_ctor_set(x_314, 0, x_311);
lean_ctor_set(x_314, 1, x_312);
return x_314;
}
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
lean_dec(x_290);
lean_dec(x_287);
lean_dec(x_277);
lean_dec(x_50);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_315 = lean_ctor_get(x_294, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_294, 1);
lean_inc(x_316);
if (lean_is_exclusive(x_294)) {
 lean_ctor_release(x_294, 0);
 lean_ctor_release(x_294, 1);
 x_317 = x_294;
} else {
 lean_dec_ref(x_294);
 x_317 = lean_box(0);
}
if (lean_is_scalar(x_317)) {
 x_318 = lean_alloc_ctor(1, 2, 0);
} else {
 x_318 = x_317;
}
lean_ctor_set(x_318, 0, x_315);
lean_ctor_set(x_318, 1, x_316);
return x_318;
}
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
lean_dec(x_287);
lean_dec(x_277);
lean_dec(x_50);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_319 = lean_ctor_get(x_289, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_289, 1);
lean_inc(x_320);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 x_321 = x_289;
} else {
 lean_dec_ref(x_289);
 x_321 = lean_box(0);
}
if (lean_is_scalar(x_321)) {
 x_322 = lean_alloc_ctor(1, 2, 0);
} else {
 x_322 = x_321;
}
lean_ctor_set(x_322, 0, x_319);
lean_ctor_set(x_322, 1, x_320);
return x_322;
}
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
lean_dec(x_277);
lean_dec(x_246);
lean_dec(x_243);
lean_dec(x_50);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_323 = lean_ctor_get(x_286, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_286, 1);
lean_inc(x_324);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 lean_ctor_release(x_286, 1);
 x_325 = x_286;
} else {
 lean_dec_ref(x_286);
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
block_285:
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_281 = lean_st_ref_get(x_277, x_280);
lean_dec(x_277);
x_282 = lean_ctor_get(x_281, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 x_283 = x_281;
} else {
 lean_dec_ref(x_281);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(0, 2, 0);
} else {
 x_284 = x_283;
}
lean_ctor_set(x_284, 0, x_279);
lean_ctor_set(x_284, 1, x_282);
return x_284;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsing___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_NormCast_proveEqUsing(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_mkEq(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_mk_string_unchecked("", 0, 0);
x_13 = l_Lean_stringToMessageData(x_12);
lean_dec(x_12);
x_14 = l_Lean_exceptOptionEmoji___redArg(x_3);
x_15 = l_Lean_stringToMessageData(x_14);
lean_dec(x_14);
lean_inc(x_13);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_mk_string_unchecked(" proving: ", 10, 10);
x_18 = l_Lean_stringToMessageData(x_17);
lean_dec(x_17);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_MessageData_ofExpr(x_11);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_13);
lean_ctor_set(x_9, 0, x_22);
return x_9;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_23 = lean_ctor_get(x_9, 0);
x_24 = lean_ctor_get(x_9, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_9);
x_25 = lean_mk_string_unchecked("", 0, 0);
x_26 = l_Lean_stringToMessageData(x_25);
lean_dec(x_25);
x_27 = l_Lean_exceptOptionEmoji___redArg(x_3);
x_28 = l_Lean_stringToMessageData(x_27);
lean_dec(x_27);
lean_inc(x_26);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_mk_string_unchecked(" proving: ", 10, 10);
x_31 = l_Lean_stringToMessageData(x_30);
lean_dec(x_30);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_MessageData_ofExpr(x_23);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_26);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_24);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_9);
if (x_37 == 0)
{
return x_9;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_9, 0);
x_39 = lean_ctor_get(x_9, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_9);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Lean_Meta_SimpExtension_getTheorems___redArg(x_1, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Elab_Tactic_NormCast_proveEqUsing(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
lean_inc(x_2);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___boxed), 8, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = lean_mk_string_unchecked("Tactic", 6, 6);
x_10 = lean_mk_string_unchecked("norm_cast", 9, 9);
x_11 = l_Lean_Name_mkStr2(x_9, x_10);
x_12 = l_Lean_Meta_NormCast_normCastExt;
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__1___boxed), 8, 3);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, x_1);
lean_closure_set(x_14, 2, x_2);
x_15 = lean_box(1);
x_16 = lean_mk_string_unchecked("", 0, 0);
x_17 = lean_unbox(x_15);
x_18 = l_Lean_withTraceNode___at___Lean_Meta_processPostponed_spec__0(lean_box(0), x_11, x_8, x_14, x_17, x_16, x_3, x_4, x_5, x_6, x_7);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_mkCoe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_Meta_coerce_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 1)
{
uint8_t x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_9);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_dec(x_8);
x_17 = lean_mk_string_unchecked("failed", 6, 6);
x_18 = l_Lean_stringToMessageData(x_17);
lean_dec(x_17);
x_19 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_18, x_3, x_4, x_5, x_6, x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_8);
if (x_20 == 0)
{
return x_8;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_8, 0);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_8);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_apply_6(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___lam__0___boxed), 6, 0);
x_8 = l_Lean_Expr_getAppFn(x_1);
switch (lean_obj_tag(x_8)) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Expr_bvar___override(x_9);
x_11 = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___lam__1(x_7, x_10, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_10);
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = l_Lean_Expr_fvar___override(x_12);
x_14 = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___lam__1(x_7, x_13, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_13);
return x_14;
}
case 2:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
x_16 = l_Lean_Expr_mvar___override(x_15);
x_17 = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___lam__1(x_7, x_16, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_16);
return x_17;
}
case 3:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_8, 0);
lean_inc(x_18);
lean_dec(x_8);
x_19 = l_Lean_Expr_sort___override(x_18);
x_20 = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___lam__1(x_7, x_19, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_19);
return x_20;
}
case 4:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_7);
x_21 = lean_ctor_get(x_8, 0);
lean_inc(x_21);
lean_dec(x_8);
x_22 = l_Lean_Meta_getCoeFnInfo_x3f___redArg(x_21, x_5, x_6);
lean_dec(x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_box(0);
x_26 = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___lam__0(x_25, x_2, x_3, x_4, x_5, x_24);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_22, 1);
x_29 = lean_ctor_get(x_22, 0);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_23);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_23, 0);
x_32 = l_Lean_Expr_getAppNumArgs(x_1);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_nat_dec_eq(x_32, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_32);
lean_free_object(x_23);
lean_dec(x_31);
lean_free_object(x_22);
x_35 = lean_box(0);
x_36 = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___lam__0(x_35, x_2, x_3, x_4, x_5, x_28);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = lean_nat_sub(x_32, x_37);
lean_dec(x_37);
lean_dec(x_32);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_sub(x_38, x_39);
lean_dec(x_38);
x_41 = l_Lean_Expr_getRevArg_x21(x_1, x_40);
lean_ctor_set(x_23, 0, x_41);
return x_22;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_23, 0);
lean_inc(x_42);
lean_dec(x_23);
x_43 = l_Lean_Expr_getAppNumArgs(x_1);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = lean_nat_dec_eq(x_43, x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_43);
lean_dec(x_42);
lean_free_object(x_22);
x_46 = lean_box(0);
x_47 = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___lam__0(x_46, x_2, x_3, x_4, x_5, x_28);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_dec(x_42);
x_49 = lean_nat_sub(x_43, x_48);
lean_dec(x_48);
lean_dec(x_43);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_sub(x_49, x_50);
lean_dec(x_49);
x_52 = l_Lean_Expr_getRevArg_x21(x_1, x_51);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_22, 0, x_53);
return x_22;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_54 = lean_ctor_get(x_22, 1);
lean_inc(x_54);
lean_dec(x_22);
x_55 = lean_ctor_get(x_23, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_56 = x_23;
} else {
 lean_dec_ref(x_23);
 x_56 = lean_box(0);
}
x_57 = l_Lean_Expr_getAppNumArgs(x_1);
x_58 = lean_ctor_get(x_55, 0);
lean_inc(x_58);
x_59 = lean_nat_dec_eq(x_57, x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
x_60 = lean_box(0);
x_61 = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___lam__0(x_60, x_2, x_3, x_4, x_5, x_54);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
lean_dec(x_55);
x_63 = lean_nat_sub(x_57, x_62);
lean_dec(x_62);
lean_dec(x_57);
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_nat_sub(x_63, x_64);
lean_dec(x_63);
x_66 = l_Lean_Expr_getRevArg_x21(x_1, x_65);
if (lean_is_scalar(x_56)) {
 x_67 = lean_alloc_ctor(1, 1, 0);
} else {
 x_67 = x_56;
}
lean_ctor_set(x_67, 0, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_54);
return x_68;
}
}
}
}
case 5:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_8, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_8, 1);
lean_inc(x_70);
lean_dec(x_8);
x_71 = l_Lean_Expr_app___override(x_69, x_70);
x_72 = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___lam__1(x_7, x_71, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_71);
return x_72;
}
case 6:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_8, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_8, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_8, 2);
lean_inc(x_75);
x_76 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 8);
lean_dec(x_8);
x_77 = l_Lean_Expr_lam___override(x_73, x_74, x_75, x_76);
x_78 = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___lam__1(x_7, x_77, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_77);
return x_78;
}
case 7:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; 
x_79 = lean_ctor_get(x_8, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_8, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_8, 2);
lean_inc(x_81);
x_82 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 8);
lean_dec(x_8);
x_83 = l_Lean_Expr_forallE___override(x_79, x_80, x_81, x_82);
x_84 = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___lam__1(x_7, x_83, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_83);
return x_84;
}
case 8:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; 
x_85 = lean_ctor_get(x_8, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_8, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_8, 2);
lean_inc(x_87);
x_88 = lean_ctor_get(x_8, 3);
lean_inc(x_88);
x_89 = lean_ctor_get_uint8(x_8, sizeof(void*)*4 + 8);
lean_dec(x_8);
x_90 = l_Lean_Expr_letE___override(x_85, x_86, x_87, x_88, x_89);
x_91 = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___lam__1(x_7, x_90, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_90);
return x_91;
}
case 9:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_8, 0);
lean_inc(x_92);
lean_dec(x_8);
x_93 = l_Lean_Expr_lit___override(x_92);
x_94 = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___lam__1(x_7, x_93, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_93);
return x_94;
}
case 10:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_8, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_8, 1);
lean_inc(x_96);
lean_dec(x_8);
x_97 = l_Lean_Expr_mdata___override(x_95, x_96);
x_98 = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___lam__1(x_7, x_97, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_97);
return x_98;
}
default: 
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_99 = lean_ctor_get(x_8, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_8, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_8, 2);
lean_inc(x_101);
lean_dec(x_8);
x_102 = l_Lean_Expr_proj___override(x_99, x_100, x_101);
x_103 = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___lam__1(x_7, x_102, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_102);
return x_103;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("zero", 4, 4);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = l_Lean_Expr_isConstOf(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = l_Lean_Expr_consumeMData(x_1);
if (lean_obj_tag(x_6) == 5)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 5)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 5)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 4)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_box(0);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_mk_string_unchecked("OfNat", 5, 5);
x_19 = lean_string_dec_eq(x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
if (x_19 == 0)
{
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
if (lean_obj_tag(x_16) == 0)
{
return x_13;
}
else
{
lean_dec(x_16);
return x_13;
}
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_mk_string_unchecked("ofNat", 5, 5);
x_21 = lean_string_dec_eq(x_15, x_20);
lean_dec(x_20);
lean_dec(x_15);
if (x_21 == 0)
{
lean_dec(x_11);
lean_dec(x_10);
if (lean_obj_tag(x_16) == 0)
{
return x_13;
}
else
{
lean_dec(x_16);
return x_13;
}
}
else
{
if (lean_obj_tag(x_10) == 9)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_10, 0);
lean_inc(x_22);
lean_dec(x_10);
if (lean_obj_tag(x_22) == 0)
{
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_11);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
else
{
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_11);
return x_13;
}
}
else
{
lean_dec(x_22);
lean_dec(x_11);
if (lean_obj_tag(x_16) == 0)
{
return x_13;
}
else
{
lean_dec(x_16);
return x_13;
}
}
}
else
{
lean_dec(x_11);
lean_dec(x_10);
if (lean_obj_tag(x_16) == 0)
{
return x_13;
}
else
{
lean_dec(x_16);
return x_13;
}
}
}
}
}
else
{
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_13;
}
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_13;
}
}
else
{
lean_object* x_29; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_29 = lean_box(0);
return x_29;
}
}
else
{
lean_object* x_30; 
lean_dec(x_8);
lean_dec(x_7);
x_30 = lean_box(0);
return x_30;
}
}
else
{
lean_object* x_31; 
lean_dec(x_7);
x_31 = lean_box(0);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_6);
x_32 = lean_box(0);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = l_Lean_Name_mkStr1(x_2);
x_34 = lean_box(0);
x_35 = l_Lean_Expr_const___override(x_33, x_34);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_box(0);
x_9 = lean_box(1);
x_10 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*2, x_11);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_147; lean_object* x_148; uint8_t x_149; lean_object* x_242; lean_object* x_243; lean_object* x_247; lean_object* x_251; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_251 = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f(x_3, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
x_254 = lean_mk_string_unchecked("failed", 6, 6);
x_255 = l_Lean_stringToMessageData(x_254);
lean_dec(x_254);
x_256 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_255, x_8, x_9, x_10, x_11, x_253);
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec(x_256);
x_242 = x_257;
x_243 = x_258;
goto block_246;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_251, 1);
lean_inc(x_259);
lean_dec(x_251);
x_260 = lean_ctor_get(x_252, 0);
lean_inc(x_260);
lean_dec(x_252);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_261 = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f(x_5, x_8, x_9, x_10, x_11, x_259);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_dec(x_260);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec(x_261);
x_264 = lean_mk_string_unchecked("failed", 6, 6);
x_265 = l_Lean_stringToMessageData(x_264);
lean_dec(x_264);
x_266 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_265, x_8, x_9, x_10, x_11, x_263);
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
lean_dec(x_266);
x_242 = x_267;
x_243 = x_268;
goto block_246;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = lean_ctor_get(x_261, 1);
lean_inc(x_269);
lean_dec(x_261);
x_270 = lean_ctor_get(x_262, 0);
lean_inc(x_270);
lean_dec(x_262);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_260);
x_271 = lean_infer_type(x_260, x_8, x_9, x_10, x_11, x_269);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; lean_object* x_302; lean_object* x_303; lean_object* x_307; lean_object* x_311; 
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
lean_dec(x_271);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_270);
x_311 = lean_infer_type(x_270, x_8, x_9, x_10, x_11, x_273);
if (lean_obj_tag(x_311) == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_311, 1);
lean_inc(x_313);
lean_dec(x_311);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_314 = l_Lean_Elab_Tactic_NormCast_mkCoe(x_260, x_312, x_8, x_9, x_10, x_11, x_313);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_314, 1);
lean_inc(x_316);
lean_dec(x_314);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
x_317 = l_Lean_Elab_Tactic_NormCast_mkCoe(x_315, x_6, x_8, x_9, x_10, x_11, x_316);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_317, 1);
lean_inc(x_319);
lean_dec(x_317);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
x_320 = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(x_3, x_318, x_8, x_9, x_10, x_11, x_319);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; 
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
if (lean_obj_tag(x_321) == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_322 = lean_ctor_get(x_320, 1);
lean_inc(x_322);
lean_dec(x_320);
x_323 = lean_mk_string_unchecked("failed", 6, 6);
x_324 = l_Lean_stringToMessageData(x_323);
lean_dec(x_323);
x_325 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_324, x_8, x_9, x_10, x_11, x_322);
x_307 = x_325;
goto block_310;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_326 = lean_ctor_get(x_320, 1);
lean_inc(x_326);
lean_dec(x_320);
x_327 = lean_ctor_get(x_321, 0);
lean_inc(x_327);
lean_dec(x_321);
x_328 = lean_box(0);
lean_inc(x_7);
x_329 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_329, 0, x_7);
lean_ctor_set(x_329, 1, x_328);
lean_ctor_set_uint8(x_329, sizeof(void*)*2, x_2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_330 = l_Lean_Meta_Simp_mkCongr(x_329, x_327, x_8, x_9, x_10, x_11, x_326);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_330, 1);
lean_inc(x_332);
lean_dec(x_330);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_5);
x_333 = l_Lean_Meta_Simp_mkCongrFun(x_331, x_5, x_8, x_9, x_10, x_11, x_332);
x_307 = x_333;
goto block_310;
}
else
{
x_307 = x_330;
goto block_310;
}
}
}
else
{
lean_object* x_334; lean_object* x_335; 
x_334 = lean_ctor_get(x_320, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_320, 1);
lean_inc(x_335);
lean_dec(x_320);
x_302 = x_334;
x_303 = x_335;
goto block_306;
}
}
else
{
lean_object* x_336; lean_object* x_337; 
x_336 = lean_ctor_get(x_317, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_317, 1);
lean_inc(x_337);
lean_dec(x_317);
x_302 = x_336;
x_303 = x_337;
goto block_306;
}
}
else
{
lean_object* x_338; lean_object* x_339; 
x_338 = lean_ctor_get(x_314, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_314, 1);
lean_inc(x_339);
lean_dec(x_314);
x_302 = x_338;
x_303 = x_339;
goto block_306;
}
}
else
{
lean_object* x_340; lean_object* x_341; 
lean_dec(x_272);
lean_dec(x_270);
lean_dec(x_260);
x_340 = lean_ctor_get(x_311, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_311, 1);
lean_inc(x_341);
lean_dec(x_311);
x_242 = x_340;
x_243 = x_341;
goto block_246;
}
block_301:
{
if (x_276 == 0)
{
lean_object* x_277; 
lean_dec(x_275);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_277 = l_Lean_Elab_Tactic_NormCast_mkCoe(x_270, x_272, x_8, x_9, x_10, x_11, x_274);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_277, 1);
lean_inc(x_279);
lean_dec(x_277);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
x_280 = l_Lean_Elab_Tactic_NormCast_mkCoe(x_278, x_6, x_8, x_9, x_10, x_11, x_279);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_280, 1);
lean_inc(x_282);
lean_dec(x_280);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_5);
x_283 = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(x_5, x_281, x_8, x_9, x_10, x_11, x_282);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; 
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_285 = lean_ctor_get(x_283, 1);
lean_inc(x_285);
lean_dec(x_283);
x_286 = lean_mk_string_unchecked("failed", 6, 6);
x_287 = l_Lean_stringToMessageData(x_286);
lean_dec(x_286);
x_288 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_287, x_8, x_9, x_10, x_11, x_285);
x_247 = x_288;
goto block_250;
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_289 = lean_ctor_get(x_283, 1);
lean_inc(x_289);
lean_dec(x_283);
x_290 = lean_ctor_get(x_284, 0);
lean_inc(x_290);
lean_dec(x_284);
lean_inc(x_3);
lean_inc(x_7);
x_291 = l_Lean_Expr_app___override(x_7, x_3);
x_292 = lean_box(0);
x_293 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_293, 0, x_291);
lean_ctor_set(x_293, 1, x_292);
lean_ctor_set_uint8(x_293, sizeof(void*)*2, x_2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_294 = l_Lean_Meta_Simp_mkCongr(x_293, x_290, x_8, x_9, x_10, x_11, x_289);
x_247 = x_294;
goto block_250;
}
}
else
{
lean_object* x_295; lean_object* x_296; 
x_295 = lean_ctor_get(x_283, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_283, 1);
lean_inc(x_296);
lean_dec(x_283);
x_242 = x_295;
x_243 = x_296;
goto block_246;
}
}
else
{
lean_object* x_297; lean_object* x_298; 
x_297 = lean_ctor_get(x_280, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_280, 1);
lean_inc(x_298);
lean_dec(x_280);
x_242 = x_297;
x_243 = x_298;
goto block_246;
}
}
else
{
lean_object* x_299; lean_object* x_300; 
x_299 = lean_ctor_get(x_277, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_277, 1);
lean_inc(x_300);
lean_dec(x_277);
x_242 = x_299;
x_243 = x_300;
goto block_246;
}
}
else
{
lean_dec(x_272);
lean_dec(x_270);
x_242 = x_275;
x_243 = x_274;
goto block_246;
}
}
block_306:
{
uint8_t x_304; 
x_304 = l_Lean_Exception_isInterrupt(x_302);
if (x_304 == 0)
{
uint8_t x_305; 
x_305 = l_Lean_Exception_isRuntime(x_302);
x_274 = x_303;
x_275 = x_302;
x_276 = x_305;
goto block_301;
}
else
{
x_274 = x_303;
x_275 = x_302;
x_276 = x_304;
goto block_301;
}
}
block_310:
{
if (lean_obj_tag(x_307) == 0)
{
lean_dec(x_272);
lean_dec(x_270);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_307;
}
else
{
lean_object* x_308; lean_object* x_309; 
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_307, 1);
lean_inc(x_309);
lean_dec(x_307);
x_302 = x_308;
x_303 = x_309;
goto block_306;
}
}
}
else
{
lean_object* x_342; lean_object* x_343; 
lean_dec(x_270);
lean_dec(x_260);
x_342 = lean_ctor_get(x_271, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_271, 1);
lean_inc(x_343);
lean_dec(x_271);
x_242 = x_342;
x_243 = x_343;
goto block_246;
}
}
}
else
{
lean_object* x_344; lean_object* x_345; 
lean_dec(x_260);
x_344 = lean_ctor_get(x_261, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_261, 1);
lean_inc(x_345);
lean_dec(x_261);
x_242 = x_344;
x_243 = x_345;
goto block_246;
}
}
}
else
{
lean_object* x_346; lean_object* x_347; 
x_346 = lean_ctor_get(x_251, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_251, 1);
lean_inc(x_347);
lean_dec(x_251);
x_242 = x_346;
x_243 = x_347;
goto block_246;
}
block_25:
{
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
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
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
block_32:
{
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_27);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_2);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
return x_31;
}
else
{
lean_dec(x_26);
lean_dec(x_1);
x_13 = x_27;
goto block_25;
}
}
block_38:
{
uint8_t x_36; 
x_36 = l_Lean_Exception_isInterrupt(x_34);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = l_Lean_Exception_isRuntime(x_34);
lean_dec(x_34);
x_26 = x_35;
x_27 = x_33;
x_28 = x_37;
goto block_32;
}
else
{
lean_dec(x_34);
x_26 = x_35;
x_27 = x_33;
x_28 = x_36;
goto block_32;
}
}
block_140:
{
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_39);
x_42 = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(x_3);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_43 = lean_apply_6(x_4, x_42, x_8, x_9, x_10, x_11, x_40);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec(x_45);
lean_ctor_set(x_43, 0, x_46);
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_43, 0);
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_43);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_43, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_43, 1);
lean_inc(x_52);
x_33 = x_43;
x_34 = x_51;
x_35 = x_52;
goto block_38;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_4);
x_53 = lean_ctor_get(x_42, 0);
lean_inc(x_53);
lean_dec(x_42);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_55 = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f(x_5, x_8, x_9, x_10, x_11, x_40);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_dec(x_54);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_mk_string_unchecked("failed", 6, 6);
x_59 = l_Lean_stringToMessageData(x_58);
lean_dec(x_58);
x_60 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_59, x_8, x_9, x_10, x_11, x_57);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_inc(x_62);
x_33 = x_60;
x_34 = x_62;
x_35 = x_63;
goto block_38;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_60, 0);
x_65 = lean_ctor_get(x_60, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_60);
lean_inc(x_65);
lean_inc(x_64);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_33 = x_66;
x_34 = x_64;
x_35 = x_65;
goto block_38;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_55, 1);
lean_inc(x_67);
lean_dec(x_55);
x_68 = lean_ctor_get(x_56, 0);
lean_inc(x_68);
lean_dec(x_56);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_69 = lean_infer_type(x_68, x_8, x_9, x_10, x_11, x_67);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_72 = l_Lean_Meta_mkNumeral(x_70, x_54, x_8, x_9, x_10, x_11, x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_75 = l_Lean_Elab_Tactic_NormCast_mkCoe(x_73, x_6, x_8, x_9, x_10, x_11, x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_78 = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(x_3, x_76, x_8, x_9, x_10, x_11, x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
lean_dec(x_7);
lean_dec(x_5);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_mk_string_unchecked("failed", 6, 6);
x_82 = l_Lean_stringToMessageData(x_81);
lean_dec(x_81);
x_83 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_82, x_8, x_9, x_10, x_11, x_80);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_83, 0);
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
lean_inc(x_85);
x_33 = x_83;
x_34 = x_85;
x_35 = x_86;
goto block_38;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_83, 0);
x_88 = lean_ctor_get(x_83, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_83);
lean_inc(x_88);
lean_inc(x_87);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_33 = x_89;
x_34 = x_87;
x_35 = x_88;
goto block_38;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_78, 1);
lean_inc(x_90);
lean_dec(x_78);
x_91 = lean_ctor_get(x_79, 0);
lean_inc(x_91);
lean_dec(x_79);
x_92 = lean_box(0);
x_93 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_93, 0, x_7);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set_uint8(x_93, sizeof(void*)*2, x_2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_94 = l_Lean_Meta_Simp_mkCongr(x_93, x_91, x_8, x_9, x_10, x_11, x_90);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = l_Lean_Meta_Simp_mkCongrFun(x_95, x_5, x_8, x_9, x_10, x_11, x_96);
if (lean_obj_tag(x_97) == 0)
{
lean_dec(x_1);
return x_97;
}
else
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_97, 0);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_inc(x_99);
x_33 = x_97;
x_34 = x_99;
x_35 = x_100;
goto block_38;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_97, 0);
x_102 = lean_ctor_get(x_97, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_97);
lean_inc(x_102);
lean_inc(x_101);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_33 = x_103;
x_34 = x_101;
x_35 = x_102;
goto block_38;
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_104 = !lean_is_exclusive(x_94);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_94, 0);
x_106 = lean_ctor_get(x_94, 1);
lean_inc(x_106);
lean_inc(x_105);
x_33 = x_94;
x_34 = x_105;
x_35 = x_106;
goto block_38;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_94, 0);
x_108 = lean_ctor_get(x_94, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_94);
lean_inc(x_108);
lean_inc(x_107);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
x_33 = x_109;
x_34 = x_107;
x_35 = x_108;
goto block_38;
}
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_110 = !lean_is_exclusive(x_78);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_78, 0);
x_112 = lean_ctor_get(x_78, 1);
lean_inc(x_112);
lean_inc(x_111);
x_33 = x_78;
x_34 = x_111;
x_35 = x_112;
goto block_38;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_78, 0);
x_114 = lean_ctor_get(x_78, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_78);
lean_inc(x_114);
lean_inc(x_113);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
x_33 = x_115;
x_34 = x_113;
x_35 = x_114;
goto block_38;
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_116 = !lean_is_exclusive(x_75);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_75, 0);
x_118 = lean_ctor_get(x_75, 1);
lean_inc(x_118);
lean_inc(x_117);
x_33 = x_75;
x_34 = x_117;
x_35 = x_118;
goto block_38;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_75, 0);
x_120 = lean_ctor_get(x_75, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_75);
lean_inc(x_120);
lean_inc(x_119);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
x_33 = x_121;
x_34 = x_119;
x_35 = x_120;
goto block_38;
}
}
}
else
{
uint8_t x_122; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_122 = !lean_is_exclusive(x_72);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_72, 0);
x_124 = lean_ctor_get(x_72, 1);
lean_inc(x_124);
lean_inc(x_123);
x_33 = x_72;
x_34 = x_123;
x_35 = x_124;
goto block_38;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_72, 0);
x_126 = lean_ctor_get(x_72, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_72);
lean_inc(x_126);
lean_inc(x_125);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
x_33 = x_127;
x_34 = x_125;
x_35 = x_126;
goto block_38;
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_54);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_128 = !lean_is_exclusive(x_69);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_69, 0);
x_130 = lean_ctor_get(x_69, 1);
lean_inc(x_130);
lean_inc(x_129);
x_33 = x_69;
x_34 = x_129;
x_35 = x_130;
goto block_38;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_69, 0);
x_132 = lean_ctor_get(x_69, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_69);
lean_inc(x_132);
lean_inc(x_131);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_33 = x_133;
x_34 = x_131;
x_35 = x_132;
goto block_38;
}
}
}
}
else
{
uint8_t x_134; 
lean_dec(x_54);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_134 = !lean_is_exclusive(x_55);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_55, 0);
x_136 = lean_ctor_get(x_55, 1);
lean_inc(x_136);
lean_inc(x_135);
x_33 = x_55;
x_34 = x_135;
x_35 = x_136;
goto block_38;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_55, 0);
x_138 = lean_ctor_get(x_55, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_55);
lean_inc(x_138);
lean_inc(x_137);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
x_33 = x_139;
x_34 = x_137;
x_35 = x_138;
goto block_38;
}
}
}
}
else
{
lean_dec(x_40);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_13 = x_39;
goto block_25;
}
}
block_146:
{
uint8_t x_144; 
x_144 = l_Lean_Exception_isInterrupt(x_142);
if (x_144 == 0)
{
uint8_t x_145; 
x_145 = l_Lean_Exception_isRuntime(x_142);
lean_dec(x_142);
x_39 = x_141;
x_40 = x_143;
x_41 = x_145;
goto block_140;
}
else
{
lean_dec(x_142);
x_39 = x_141;
x_40 = x_143;
x_41 = x_144;
goto block_140;
}
}
block_241:
{
if (x_149 == 0)
{
lean_object* x_150; 
lean_dec(x_148);
x_150 = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(x_5);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; 
lean_inc(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_151 = lean_apply_6(x_4, x_150, x_8, x_9, x_10, x_11, x_147);
if (lean_obj_tag(x_151) == 0)
{
uint8_t x_152; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_152 = !lean_is_exclusive(x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_151, 0);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
lean_dec(x_153);
lean_ctor_set(x_151, 0, x_154);
return x_151;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_155 = lean_ctor_get(x_151, 0);
x_156 = lean_ctor_get(x_151, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_151);
x_157 = lean_ctor_get(x_155, 0);
lean_inc(x_157);
lean_dec(x_155);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_151, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_151, 1);
lean_inc(x_160);
x_141 = x_151;
x_142 = x_159;
x_143 = x_160;
goto block_146;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_150, 0);
lean_inc(x_161);
lean_dec(x_150);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
lean_dec(x_161);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_163 = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f(x_3, x_8, x_9, x_10, x_11, x_147);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; 
lean_dec(x_162);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_mk_string_unchecked("failed", 6, 6);
x_167 = l_Lean_stringToMessageData(x_166);
lean_dec(x_166);
x_168 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_167, x_8, x_9, x_10, x_11, x_165);
x_169 = !lean_is_exclusive(x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_ctor_get(x_168, 0);
x_171 = lean_ctor_get(x_168, 1);
lean_inc(x_171);
lean_inc(x_170);
x_141 = x_168;
x_142 = x_170;
x_143 = x_171;
goto block_146;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_168, 0);
x_173 = lean_ctor_get(x_168, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_168);
lean_inc(x_173);
lean_inc(x_172);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
x_141 = x_174;
x_142 = x_172;
x_143 = x_173;
goto block_146;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_163, 1);
lean_inc(x_175);
lean_dec(x_163);
x_176 = lean_ctor_get(x_164, 0);
lean_inc(x_176);
lean_dec(x_164);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_177 = lean_infer_type(x_176, x_8, x_9, x_10, x_11, x_175);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_180 = l_Lean_Meta_mkNumeral(x_178, x_162, x_8, x_9, x_10, x_11, x_179);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
x_183 = l_Lean_Elab_Tactic_NormCast_mkCoe(x_181, x_6, x_8, x_9, x_10, x_11, x_182);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_5);
x_186 = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(x_5, x_184, x_8, x_9, x_10, x_11, x_185);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
x_189 = lean_mk_string_unchecked("failed", 6, 6);
x_190 = l_Lean_stringToMessageData(x_189);
lean_dec(x_189);
x_191 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_190, x_8, x_9, x_10, x_11, x_188);
x_192 = !lean_is_exclusive(x_191);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; 
x_193 = lean_ctor_get(x_191, 0);
x_194 = lean_ctor_get(x_191, 1);
lean_inc(x_194);
lean_inc(x_193);
x_141 = x_191;
x_142 = x_193;
x_143 = x_194;
goto block_146;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_191, 0);
x_196 = lean_ctor_get(x_191, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_191);
lean_inc(x_196);
lean_inc(x_195);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
x_141 = x_197;
x_142 = x_195;
x_143 = x_196;
goto block_146;
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_198 = lean_ctor_get(x_186, 1);
lean_inc(x_198);
lean_dec(x_186);
x_199 = lean_ctor_get(x_187, 0);
lean_inc(x_199);
lean_dec(x_187);
lean_inc(x_3);
lean_inc(x_7);
x_200 = l_Lean_Expr_app___override(x_7, x_3);
x_201 = lean_box(0);
x_202 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
lean_ctor_set_uint8(x_202, sizeof(void*)*2, x_2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_203 = l_Lean_Meta_Simp_mkCongr(x_202, x_199, x_8, x_9, x_10, x_11, x_198);
if (lean_obj_tag(x_203) == 0)
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_203;
}
else
{
uint8_t x_204; 
x_204 = !lean_is_exclusive(x_203);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_203, 0);
x_206 = lean_ctor_get(x_203, 1);
lean_inc(x_206);
lean_inc(x_205);
x_141 = x_203;
x_142 = x_205;
x_143 = x_206;
goto block_146;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_203, 0);
x_208 = lean_ctor_get(x_203, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_203);
lean_inc(x_208);
lean_inc(x_207);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
x_141 = x_209;
x_142 = x_207;
x_143 = x_208;
goto block_146;
}
}
}
}
else
{
uint8_t x_210; 
x_210 = !lean_is_exclusive(x_186);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_186, 0);
x_212 = lean_ctor_get(x_186, 1);
lean_inc(x_212);
lean_inc(x_211);
x_141 = x_186;
x_142 = x_211;
x_143 = x_212;
goto block_146;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_186, 0);
x_214 = lean_ctor_get(x_186, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_186);
lean_inc(x_214);
lean_inc(x_213);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
x_141 = x_215;
x_142 = x_213;
x_143 = x_214;
goto block_146;
}
}
}
else
{
uint8_t x_216; 
x_216 = !lean_is_exclusive(x_183);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; 
x_217 = lean_ctor_get(x_183, 0);
x_218 = lean_ctor_get(x_183, 1);
lean_inc(x_218);
lean_inc(x_217);
x_141 = x_183;
x_142 = x_217;
x_143 = x_218;
goto block_146;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_183, 0);
x_220 = lean_ctor_get(x_183, 1);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_183);
lean_inc(x_220);
lean_inc(x_219);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
x_141 = x_221;
x_142 = x_219;
x_143 = x_220;
goto block_146;
}
}
}
else
{
uint8_t x_222; 
x_222 = !lean_is_exclusive(x_180);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; 
x_223 = lean_ctor_get(x_180, 0);
x_224 = lean_ctor_get(x_180, 1);
lean_inc(x_224);
lean_inc(x_223);
x_141 = x_180;
x_142 = x_223;
x_143 = x_224;
goto block_146;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_180, 0);
x_226 = lean_ctor_get(x_180, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_180);
lean_inc(x_226);
lean_inc(x_225);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
x_141 = x_227;
x_142 = x_225;
x_143 = x_226;
goto block_146;
}
}
}
else
{
uint8_t x_228; 
lean_dec(x_162);
x_228 = !lean_is_exclusive(x_177);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_ctor_get(x_177, 0);
x_230 = lean_ctor_get(x_177, 1);
lean_inc(x_230);
lean_inc(x_229);
x_141 = x_177;
x_142 = x_229;
x_143 = x_230;
goto block_146;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_177, 0);
x_232 = lean_ctor_get(x_177, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_177);
lean_inc(x_232);
lean_inc(x_231);
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
x_141 = x_233;
x_142 = x_231;
x_143 = x_232;
goto block_146;
}
}
}
}
else
{
uint8_t x_234; 
lean_dec(x_162);
x_234 = !lean_is_exclusive(x_163);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; 
x_235 = lean_ctor_get(x_163, 0);
x_236 = lean_ctor_get(x_163, 1);
lean_inc(x_236);
lean_inc(x_235);
x_141 = x_163;
x_142 = x_235;
x_143 = x_236;
goto block_146;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_163, 0);
x_238 = lean_ctor_get(x_163, 1);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_163);
lean_inc(x_238);
lean_inc(x_237);
x_239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
x_141 = x_239;
x_142 = x_237;
x_143 = x_238;
goto block_146;
}
}
}
}
else
{
lean_object* x_240; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_240 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_240, 0, x_148);
lean_ctor_set(x_240, 1, x_147);
return x_240;
}
}
block_246:
{
uint8_t x_244; 
x_244 = l_Lean_Exception_isInterrupt(x_242);
if (x_244 == 0)
{
uint8_t x_245; 
x_245 = l_Lean_Exception_isRuntime(x_242);
x_147 = x_243;
x_148 = x_242;
x_149 = x_245;
goto block_241;
}
else
{
x_147 = x_243;
x_148 = x_242;
x_149 = x_244;
goto block_241;
}
}
block_250:
{
if (lean_obj_tag(x_247) == 0)
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_247;
}
else
{
lean_object* x_248; lean_object* x_249; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec(x_247);
x_242 = x_248;
x_243 = x_249;
goto block_246;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
x_10 = lean_mk_string_unchecked("💥️", 7, 2);
x_11 = l_Lean_stringToMessageData(x_10);
lean_dec(x_10);
lean_inc(x_1);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_mk_string_unchecked(" ", 1, 1);
x_14 = l_Lean_stringToMessageData(x_13);
lean_dec(x_13);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_2);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_4, 0);
lean_inc(x_19);
lean_dec(x_4);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_expr_eqv(x_20, x_3);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_22 = lean_mk_string_unchecked("✅️", 6, 2);
x_23 = l_Lean_stringToMessageData(x_22);
lean_dec(x_22);
lean_inc(x_1);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_mk_string_unchecked(" ", 1, 1);
x_26 = l_Lean_stringToMessageData(x_25);
lean_dec(x_25);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_2);
x_29 = lean_mk_string_unchecked(" to ", 4, 4);
x_30 = l_Lean_stringToMessageData(x_29);
lean_dec(x_29);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_MessageData_ofExpr(x_20);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_1);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_9);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_20);
x_36 = lean_mk_string_unchecked("❌️", 6, 2);
x_37 = l_Lean_stringToMessageData(x_36);
lean_dec(x_36);
lean_inc(x_1);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_mk_string_unchecked(" ", 1, 1);
x_40 = l_Lean_stringToMessageData(x_39);
lean_dec(x_39);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_2);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_1);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_9);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
switch (lean_obj_tag(x_7)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Expr_bvar___override(x_9);
x_11 = l_Lean_Expr_app___override(x_10, x_8);
x_12 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(x_1, x_11, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
lean_dec(x_7);
x_15 = l_Lean_Expr_fvar___override(x_14);
x_16 = l_Lean_Expr_app___override(x_15, x_13);
x_17 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(x_1, x_16, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_16);
return x_17;
}
case 2:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_7, 0);
lean_inc(x_19);
lean_dec(x_7);
x_20 = l_Lean_Expr_mvar___override(x_19);
x_21 = l_Lean_Expr_app___override(x_20, x_18);
x_22 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(x_1, x_21, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_21);
return x_22;
}
case 3:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_7, 0);
lean_inc(x_24);
lean_dec(x_7);
x_25 = l_Lean_Expr_sort___override(x_24);
x_26 = l_Lean_Expr_app___override(x_25, x_23);
x_27 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(x_1, x_26, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_26);
return x_27;
}
case 4:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_7, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_7, 1);
lean_inc(x_30);
lean_dec(x_7);
x_31 = l_Lean_Expr_const___override(x_29, x_30);
x_32 = l_Lean_Expr_app___override(x_31, x_28);
x_33 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(x_1, x_32, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_32);
return x_33;
}
case 5:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_7, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_7, 1);
lean_inc(x_36);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_35);
x_37 = lean_infer_type(x_35, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 7)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 2);
lean_inc(x_39);
switch (lean_obj_tag(x_39)) {
case 0:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
x_43 = lean_ctor_get_uint8(x_38, sizeof(void*)*3 + 8);
lean_dec(x_38);
x_44 = lean_ctor_get(x_39, 0);
lean_inc(x_44);
lean_dec(x_39);
x_45 = l_Lean_Expr_bvar___override(x_44);
x_46 = l_Lean_Expr_forallE___override(x_41, x_42, x_45, x_43);
x_47 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(x_1, x_46, x_2, x_3, x_4, x_5, x_40);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_46);
return x_47;
}
case 1:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
x_48 = lean_ctor_get(x_37, 1);
lean_inc(x_48);
lean_dec(x_37);
x_49 = lean_ctor_get(x_38, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_38, 1);
lean_inc(x_50);
x_51 = lean_ctor_get_uint8(x_38, sizeof(void*)*3 + 8);
lean_dec(x_38);
x_52 = lean_ctor_get(x_39, 0);
lean_inc(x_52);
lean_dec(x_39);
x_53 = l_Lean_Expr_fvar___override(x_52);
x_54 = l_Lean_Expr_forallE___override(x_49, x_50, x_53, x_51);
x_55 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(x_1, x_54, x_2, x_3, x_4, x_5, x_48);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_54);
return x_55;
}
case 2:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
x_56 = lean_ctor_get(x_37, 1);
lean_inc(x_56);
lean_dec(x_37);
x_57 = lean_ctor_get(x_38, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_38, 1);
lean_inc(x_58);
x_59 = lean_ctor_get_uint8(x_38, sizeof(void*)*3 + 8);
lean_dec(x_38);
x_60 = lean_ctor_get(x_39, 0);
lean_inc(x_60);
lean_dec(x_39);
x_61 = l_Lean_Expr_mvar___override(x_60);
x_62 = l_Lean_Expr_forallE___override(x_57, x_58, x_61, x_59);
x_63 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(x_1, x_62, x_2, x_3, x_4, x_5, x_56);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_62);
return x_63;
}
case 3:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
x_64 = lean_ctor_get(x_37, 1);
lean_inc(x_64);
lean_dec(x_37);
x_65 = lean_ctor_get(x_38, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_38, 1);
lean_inc(x_66);
x_67 = lean_ctor_get_uint8(x_38, sizeof(void*)*3 + 8);
lean_dec(x_38);
x_68 = lean_ctor_get(x_39, 0);
lean_inc(x_68);
lean_dec(x_39);
x_69 = l_Lean_Expr_sort___override(x_68);
x_70 = l_Lean_Expr_forallE___override(x_65, x_66, x_69, x_67);
x_71 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(x_1, x_70, x_2, x_3, x_4, x_5, x_64);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_70);
return x_71;
}
case 4:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
x_72 = lean_ctor_get(x_37, 1);
lean_inc(x_72);
lean_dec(x_37);
x_73 = lean_ctor_get(x_38, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_38, 1);
lean_inc(x_74);
x_75 = lean_ctor_get_uint8(x_38, sizeof(void*)*3 + 8);
lean_dec(x_38);
x_76 = lean_ctor_get(x_39, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_39, 1);
lean_inc(x_77);
lean_dec(x_39);
x_78 = l_Lean_Expr_const___override(x_76, x_77);
x_79 = l_Lean_Expr_forallE___override(x_73, x_74, x_78, x_75);
x_80 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(x_1, x_79, x_2, x_3, x_4, x_5, x_72);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_79);
return x_80;
}
case 5:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
x_81 = lean_ctor_get(x_37, 1);
lean_inc(x_81);
lean_dec(x_37);
x_82 = lean_ctor_get(x_38, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_38, 1);
lean_inc(x_83);
x_84 = lean_ctor_get_uint8(x_38, sizeof(void*)*3 + 8);
lean_dec(x_38);
x_85 = lean_ctor_get(x_39, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_39, 1);
lean_inc(x_86);
lean_dec(x_39);
x_87 = l_Lean_Expr_app___override(x_85, x_86);
x_88 = l_Lean_Expr_forallE___override(x_82, x_83, x_87, x_84);
x_89 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(x_1, x_88, x_2, x_3, x_4, x_5, x_81);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_88);
return x_89;
}
case 6:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
x_90 = lean_ctor_get(x_37, 1);
lean_inc(x_90);
lean_dec(x_37);
x_91 = lean_ctor_get(x_38, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_38, 1);
lean_inc(x_92);
x_93 = lean_ctor_get_uint8(x_38, sizeof(void*)*3 + 8);
lean_dec(x_38);
x_94 = lean_ctor_get(x_39, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_39, 1);
lean_inc(x_95);
x_96 = lean_ctor_get(x_39, 2);
lean_inc(x_96);
x_97 = lean_ctor_get_uint8(x_39, sizeof(void*)*3 + 8);
lean_dec(x_39);
x_98 = l_Lean_Expr_lam___override(x_94, x_95, x_96, x_97);
x_99 = l_Lean_Expr_forallE___override(x_91, x_92, x_98, x_93);
x_100 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(x_1, x_99, x_2, x_3, x_4, x_5, x_90);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_99);
return x_100;
}
case 7:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; uint8_t x_146; 
x_101 = lean_ctor_get(x_37, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_102 = x_37;
} else {
 lean_dec_ref(x_37);
 x_102 = lean_box(0);
}
x_103 = lean_ctor_get(x_38, 1);
lean_inc(x_103);
lean_dec(x_38);
x_104 = lean_ctor_get(x_39, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_39, 2);
lean_inc(x_105);
lean_dec(x_39);
x_106 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__2___boxed), 6, 0);
x_146 = l_Lean_Expr_hasLooseBVars(x_104);
if (x_146 == 0)
{
uint8_t x_147; 
x_147 = l_Lean_Expr_hasLooseBVars(x_105);
lean_dec(x_105);
x_107 = x_147;
goto block_145;
}
else
{
lean_dec(x_105);
x_107 = x_146;
goto block_145;
}
block_145:
{
if (x_107 == 0)
{
lean_object* x_108; 
lean_dec(x_102);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_103);
x_108 = l_Lean_Meta_isExprDefEq(x_103, x_104, x_2, x_3, x_4, x_5, x_101);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; uint8_t x_110; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_unbox(x_109);
if (x_110 == 0)
{
uint8_t x_111; 
lean_dec(x_109);
lean_dec(x_106);
lean_dec(x_103);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_111 = !lean_is_exclusive(x_108);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_112 = lean_ctor_get(x_108, 0);
lean_dec(x_112);
x_113 = lean_box(1);
x_114 = lean_box(0);
x_115 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_115, 0, x_1);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_unbox(x_113);
lean_ctor_set_uint8(x_115, sizeof(void*)*2, x_116);
lean_ctor_set(x_108, 0, x_115);
return x_108;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; 
x_117 = lean_ctor_get(x_108, 1);
lean_inc(x_117);
lean_dec(x_108);
x_118 = lean_box(1);
x_119 = lean_box(0);
x_120 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_120, 0, x_1);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_unbox(x_118);
lean_ctor_set_uint8(x_120, sizeof(void*)*2, x_121);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_117);
return x_122;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; 
x_123 = lean_ctor_get(x_108, 1);
lean_inc(x_123);
lean_dec(x_108);
lean_inc(x_109);
lean_inc(x_1);
x_124 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__1___boxed), 12, 7);
lean_closure_set(x_124, 0, x_1);
lean_closure_set(x_124, 1, x_109);
lean_closure_set(x_124, 2, x_36);
lean_closure_set(x_124, 3, x_106);
lean_closure_set(x_124, 4, x_34);
lean_closure_set(x_124, 5, x_103);
lean_closure_set(x_124, 6, x_35);
x_125 = lean_mk_string_unchecked("splitting ", 10, 10);
x_126 = l_Lean_stringToMessageData(x_125);
lean_dec(x_125);
lean_inc(x_1);
x_127 = l_Lean_MessageData_ofExpr(x_1);
x_128 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_mk_string_unchecked("", 0, 0);
x_130 = l_Lean_stringToMessageData(x_129);
lean_inc(x_130);
x_131 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__3___boxed), 9, 3);
lean_closure_set(x_132, 0, x_130);
lean_closure_set(x_132, 1, x_131);
lean_closure_set(x_132, 2, x_1);
x_133 = lean_mk_string_unchecked("Tactic", 6, 6);
x_134 = lean_mk_string_unchecked("norm_cast", 9, 9);
x_135 = l_Lean_Name_mkStr2(x_133, x_134);
x_136 = lean_unbox(x_109);
lean_dec(x_109);
x_137 = l_Lean_withTraceNode___at___Lean_Meta_processPostponed_spec__0(lean_box(0), x_135, x_132, x_124, x_136, x_129, x_2, x_3, x_4, x_5, x_123);
return x_137;
}
}
else
{
uint8_t x_138; 
lean_dec(x_106);
lean_dec(x_103);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_138 = !lean_is_exclusive(x_108);
if (x_138 == 0)
{
return x_108;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_108, 0);
x_140 = lean_ctor_get(x_108, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_108);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_106);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_142 = lean_box(0);
x_143 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_143, 0, x_1);
lean_ctor_set(x_143, 1, x_142);
lean_ctor_set_uint8(x_143, sizeof(void*)*2, x_107);
if (lean_is_scalar(x_102)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_102;
}
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_101);
return x_144;
}
}
}
case 8:
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
x_148 = lean_ctor_get(x_37, 1);
lean_inc(x_148);
lean_dec(x_37);
x_149 = lean_ctor_get(x_38, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_38, 1);
lean_inc(x_150);
x_151 = lean_ctor_get_uint8(x_38, sizeof(void*)*3 + 8);
lean_dec(x_38);
x_152 = lean_ctor_get(x_39, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_39, 1);
lean_inc(x_153);
x_154 = lean_ctor_get(x_39, 2);
lean_inc(x_154);
x_155 = lean_ctor_get(x_39, 3);
lean_inc(x_155);
x_156 = lean_ctor_get_uint8(x_39, sizeof(void*)*4 + 8);
lean_dec(x_39);
x_157 = l_Lean_Expr_letE___override(x_152, x_153, x_154, x_155, x_156);
x_158 = l_Lean_Expr_forallE___override(x_149, x_150, x_157, x_151);
x_159 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(x_1, x_158, x_2, x_3, x_4, x_5, x_148);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_158);
return x_159;
}
case 9:
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
x_160 = lean_ctor_get(x_37, 1);
lean_inc(x_160);
lean_dec(x_37);
x_161 = lean_ctor_get(x_38, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_38, 1);
lean_inc(x_162);
x_163 = lean_ctor_get_uint8(x_38, sizeof(void*)*3 + 8);
lean_dec(x_38);
x_164 = lean_ctor_get(x_39, 0);
lean_inc(x_164);
lean_dec(x_39);
x_165 = l_Lean_Expr_lit___override(x_164);
x_166 = l_Lean_Expr_forallE___override(x_161, x_162, x_165, x_163);
x_167 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(x_1, x_166, x_2, x_3, x_4, x_5, x_160);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_166);
return x_167;
}
case 10:
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
x_168 = lean_ctor_get(x_37, 1);
lean_inc(x_168);
lean_dec(x_37);
x_169 = lean_ctor_get(x_38, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_38, 1);
lean_inc(x_170);
x_171 = lean_ctor_get_uint8(x_38, sizeof(void*)*3 + 8);
lean_dec(x_38);
x_172 = lean_ctor_get(x_39, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_39, 1);
lean_inc(x_173);
lean_dec(x_39);
x_174 = l_Lean_Expr_mdata___override(x_172, x_173);
x_175 = l_Lean_Expr_forallE___override(x_169, x_170, x_174, x_171);
x_176 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(x_1, x_175, x_2, x_3, x_4, x_5, x_168);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_175);
return x_176;
}
default: 
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
x_177 = lean_ctor_get(x_37, 1);
lean_inc(x_177);
lean_dec(x_37);
x_178 = lean_ctor_get(x_38, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_38, 1);
lean_inc(x_179);
x_180 = lean_ctor_get_uint8(x_38, sizeof(void*)*3 + 8);
lean_dec(x_38);
x_181 = lean_ctor_get(x_39, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_39, 1);
lean_inc(x_182);
x_183 = lean_ctor_get(x_39, 2);
lean_inc(x_183);
lean_dec(x_39);
x_184 = l_Lean_Expr_proj___override(x_181, x_182, x_183);
x_185 = l_Lean_Expr_forallE___override(x_178, x_179, x_184, x_180);
x_186 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(x_1, x_185, x_2, x_3, x_4, x_5, x_177);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_185);
return x_186;
}
}
}
else
{
lean_object* x_187; lean_object* x_188; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
x_187 = lean_ctor_get(x_37, 1);
lean_inc(x_187);
lean_dec(x_37);
x_188 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(x_1, x_38, x_2, x_3, x_4, x_5, x_187);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_38);
return x_188;
}
}
else
{
uint8_t x_189; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_189 = !lean_is_exclusive(x_37);
if (x_189 == 0)
{
return x_37;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_37, 0);
x_191 = lean_ctor_get(x_37, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_37);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
}
case 6:
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_193 = lean_ctor_get(x_1, 1);
lean_inc(x_193);
x_194 = lean_ctor_get(x_7, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_7, 1);
lean_inc(x_195);
x_196 = lean_ctor_get(x_7, 2);
lean_inc(x_196);
x_197 = lean_ctor_get_uint8(x_7, sizeof(void*)*3 + 8);
lean_dec(x_7);
x_198 = l_Lean_Expr_lam___override(x_194, x_195, x_196, x_197);
x_199 = l_Lean_Expr_app___override(x_198, x_193);
x_200 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(x_1, x_199, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_199);
return x_200;
}
case 7:
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_201 = lean_ctor_get(x_1, 1);
lean_inc(x_201);
x_202 = lean_ctor_get(x_7, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_7, 1);
lean_inc(x_203);
x_204 = lean_ctor_get(x_7, 2);
lean_inc(x_204);
x_205 = lean_ctor_get_uint8(x_7, sizeof(void*)*3 + 8);
lean_dec(x_7);
x_206 = l_Lean_Expr_forallE___override(x_202, x_203, x_204, x_205);
x_207 = l_Lean_Expr_app___override(x_206, x_201);
x_208 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(x_1, x_207, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_207);
return x_208;
}
case 8:
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_209 = lean_ctor_get(x_1, 1);
lean_inc(x_209);
x_210 = lean_ctor_get(x_7, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_7, 1);
lean_inc(x_211);
x_212 = lean_ctor_get(x_7, 2);
lean_inc(x_212);
x_213 = lean_ctor_get(x_7, 3);
lean_inc(x_213);
x_214 = lean_ctor_get_uint8(x_7, sizeof(void*)*4 + 8);
lean_dec(x_7);
x_215 = l_Lean_Expr_letE___override(x_210, x_211, x_212, x_213, x_214);
x_216 = l_Lean_Expr_app___override(x_215, x_209);
x_217 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(x_1, x_216, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_216);
return x_217;
}
case 9:
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_218 = lean_ctor_get(x_1, 1);
lean_inc(x_218);
x_219 = lean_ctor_get(x_7, 0);
lean_inc(x_219);
lean_dec(x_7);
x_220 = l_Lean_Expr_lit___override(x_219);
x_221 = l_Lean_Expr_app___override(x_220, x_218);
x_222 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(x_1, x_221, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_221);
return x_222;
}
case 10:
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_223 = lean_ctor_get(x_1, 1);
lean_inc(x_223);
x_224 = lean_ctor_get(x_7, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_7, 1);
lean_inc(x_225);
lean_dec(x_7);
x_226 = l_Lean_Expr_mdata___override(x_224, x_225);
x_227 = l_Lean_Expr_app___override(x_226, x_223);
x_228 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(x_1, x_227, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_227);
return x_228;
}
default: 
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_229 = lean_ctor_get(x_1, 1);
lean_inc(x_229);
x_230 = lean_ctor_get(x_7, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_7, 1);
lean_inc(x_231);
x_232 = lean_ctor_get(x_7, 2);
lean_inc(x_232);
lean_dec(x_7);
x_233 = l_Lean_Expr_proj___override(x_230, x_231, x_232);
x_234 = l_Lean_Expr_app___override(x_233, x_229);
x_235 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(x_1, x_234, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_234);
return x_235;
}
}
}
else
{
lean_object* x_236; 
lean_inc(x_1);
x_236 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(x_1, x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_236;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__1(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_11 = lean_mk_string_unchecked("", 0, 0);
x_12 = l_Lean_stringToMessageData(x_11);
lean_dec(x_11);
x_13 = l_Lean_exceptOptionEmoji___redArg(x_2);
x_14 = l_Lean_stringToMessageData(x_13);
lean_dec(x_13);
lean_inc(x_12);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_mk_string_unchecked(" discharging: ", 14, 14);
x_17 = l_Lean_stringToMessageData(x_16);
lean_dec(x_16);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_MessageData_ofExpr(x_1);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_12);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_10);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_findLocalDeclWithType_x3f(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_10, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = l_Lean_Expr_fvar___override(x_21);
lean_ctor_set(x_11, 0, x_22);
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_11, 0);
lean_inc(x_23);
lean_dec(x_11);
x_24 = l_Lean_Expr_fvar___override(x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_10, 0, x_25);
return x_10;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_10, 1);
lean_inc(x_26);
lean_dec(x_10);
x_27 = lean_ctor_get(x_11, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_28 = x_11;
} else {
 lean_dec_ref(x_11);
 x_28 = lean_box(0);
}
x_29 = l_Lean_Expr_fvar___override(x_27);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(1, 1, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
return x_31;
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_10);
if (x_32 == 0)
{
return x_10;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_10, 0);
x_34 = lean_ctor_get(x_10, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_10);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_prove___lam__0___boxed), 10, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_prove___lam__1___boxed), 9, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = lean_mk_string_unchecked("Tactic", 6, 6);
x_13 = lean_mk_string_unchecked("norm_cast", 9, 9);
x_14 = l_Lean_Name_mkStr2(x_12, x_13);
x_15 = lean_box(1);
x_16 = lean_mk_string_unchecked("", 0, 0);
x_17 = lean_unbox(x_15);
x_18 = l_Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2(lean_box(0), x_14, x_10, x_11, x_17, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_NormCast_prove___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_NormCast_prove___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_upwardAndElim___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_st_ref_take(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 4);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_9);
lean_ctor_set(x_12, 3, x_10);
lean_ctor_set(x_12, 4, x_11);
x_13 = lean_st_ref_set(x_1, x_12, x_7);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_upwardAndElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_st_ref_get(x_5, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_take(x_5, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_box(1);
x_19 = lean_unsigned_to_nat(8u);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_unsigned_to_nat(2u);
x_22 = lean_nat_shiftl(x_19, x_21);
x_23 = lean_unsigned_to_nat(3u);
x_24 = lean_nat_div(x_22, x_23);
lean_dec(x_22);
x_25 = l_Nat_nextPowerOfTwo(x_24);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = lean_mk_array(x_25, x_26);
lean_ctor_set(x_14, 1, x_27);
lean_ctor_set(x_14, 0, x_20);
x_28 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_30, 0, x_14);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_unbox(x_18);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_31);
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_16, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_16, 3);
lean_inc(x_34);
x_35 = lean_ctor_get(x_16, 4);
lean_inc(x_35);
lean_dec(x_16);
x_36 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_32);
lean_ctor_set(x_36, 2, x_33);
lean_ctor_set(x_36, 3, x_34);
lean_ctor_set(x_36, 4, x_35);
x_37 = lean_st_ref_set(x_5, x_36, x_17);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_prove), 9, 0);
x_40 = lean_box(0);
x_41 = lean_ctor_get(x_1, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_1, 4);
lean_inc(x_42);
lean_dec(x_1);
x_43 = lean_mk_string_unchecked("squash", 6, 6);
x_44 = lean_ctor_get(x_12, 0);
lean_inc(x_44);
lean_dec(x_12);
x_45 = lean_ctor_get(x_3, 0);
x_46 = lean_ctor_get(x_3, 1);
x_47 = lean_ctor_get(x_3, 2);
x_48 = lean_ctor_get(x_3, 3);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
x_49 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_49, 0, x_45);
lean_ctor_set(x_49, 1, x_46);
lean_ctor_set(x_49, 2, x_47);
lean_ctor_set(x_49, 3, x_48);
lean_ctor_set(x_49, 4, x_39);
x_50 = lean_unbox(x_40);
lean_ctor_set_uint8(x_49, sizeof(void*)*5, x_50);
x_51 = lean_unbox(x_40);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_52 = l_Lean_Meta_Simp_rewrite_x3f(x_2, x_41, x_42, x_43, x_51, x_49, x_4, x_5, x_6, x_7, x_8, x_9, x_38);
lean_dec(x_43);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_53);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_53);
x_56 = l_Lean_Elab_Tactic_NormCast_upwardAndElim___lam__0(x_5, x_44, x_55, x_54);
lean_dec(x_55);
lean_dec(x_5);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_91 = lean_box(0);
lean_inc(x_2);
x_92 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_92, 0, x_2);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_unbox(x_18);
lean_ctor_set_uint8(x_92, sizeof(void*)*2, x_93);
x_58 = x_92;
goto block_90;
}
else
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_53, 0);
lean_inc(x_94);
lean_dec(x_53);
x_58 = x_94;
goto block_90;
}
block_90:
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_60 = l_Lean_Elab_Tactic_NormCast_splittingProcedure(x_59, x_6, x_7, x_8, x_9, x_57);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_Meta_Simp_Result_mkEqTrans(x_58, x_61, x_6, x_7, x_8, x_9, x_62);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = lean_ctor_get(x_63, 0);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_expr_eqv(x_66, x_2);
lean_dec(x_66);
if (x_67 == 0)
{
lean_object* x_68; 
lean_dec(x_2);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_63, 0, x_68);
return x_63;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_65);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_70, 0, x_2);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set_uint8(x_70, sizeof(void*)*2, x_67);
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_63, 0, x_71);
return x_63;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_72 = lean_ctor_get(x_63, 0);
x_73 = lean_ctor_get(x_63, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_63);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
x_75 = lean_expr_eqv(x_74, x_2);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_2);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_72);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_73);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_72);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_79, 0, x_2);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set_uint8(x_79, sizeof(void*)*2, x_75);
x_80 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_73);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_2);
x_82 = !lean_is_exclusive(x_63);
if (x_82 == 0)
{
return x_63;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_63, 0);
x_84 = lean_ctor_get(x_63, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_63);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_58);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_86 = !lean_is_exclusive(x_60);
if (x_86 == 0)
{
return x_60;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_60, 0);
x_88 = lean_ctor_get(x_60, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_60);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_95 = lean_ctor_get(x_52, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_52, 1);
lean_inc(x_96);
lean_dec(x_52);
x_97 = lean_box(0);
x_98 = l_Lean_Elab_Tactic_NormCast_upwardAndElim___lam__0(x_5, x_44, x_97, x_96);
lean_dec(x_5);
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_98, 0);
lean_dec(x_100);
lean_ctor_set_tag(x_98, 1);
lean_ctor_set(x_98, 0, x_95);
return x_98;
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_95);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; uint8_t x_139; lean_object* x_140; 
x_103 = lean_ctor_get(x_14, 0);
x_104 = lean_ctor_get(x_14, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_14);
x_105 = lean_box(1);
x_106 = lean_unsigned_to_nat(8u);
x_107 = lean_unsigned_to_nat(0u);
x_108 = lean_unsigned_to_nat(2u);
x_109 = lean_nat_shiftl(x_106, x_108);
x_110 = lean_unsigned_to_nat(3u);
x_111 = lean_nat_div(x_109, x_110);
lean_dec(x_109);
x_112 = l_Nat_nextPowerOfTwo(x_111);
lean_dec(x_111);
x_113 = lean_box(0);
x_114 = lean_mk_array(x_112, x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_107);
lean_ctor_set(x_115, 1, x_114);
x_116 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_117 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_118 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_unbox(x_105);
lean_ctor_set_uint8(x_118, sizeof(void*)*2, x_119);
x_120 = lean_ctor_get(x_103, 1);
lean_inc(x_120);
x_121 = lean_ctor_get(x_103, 2);
lean_inc(x_121);
x_122 = lean_ctor_get(x_103, 3);
lean_inc(x_122);
x_123 = lean_ctor_get(x_103, 4);
lean_inc(x_123);
lean_dec(x_103);
x_124 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_124, 0, x_118);
lean_ctor_set(x_124, 1, x_120);
lean_ctor_set(x_124, 2, x_121);
lean_ctor_set(x_124, 3, x_122);
lean_ctor_set(x_124, 4, x_123);
x_125 = lean_st_ref_set(x_5, x_124, x_104);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec(x_125);
x_127 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_prove), 9, 0);
x_128 = lean_box(0);
x_129 = lean_ctor_get(x_1, 1);
lean_inc(x_129);
x_130 = lean_ctor_get(x_1, 4);
lean_inc(x_130);
lean_dec(x_1);
x_131 = lean_mk_string_unchecked("squash", 6, 6);
x_132 = lean_ctor_get(x_12, 0);
lean_inc(x_132);
lean_dec(x_12);
x_133 = lean_ctor_get(x_3, 0);
x_134 = lean_ctor_get(x_3, 1);
x_135 = lean_ctor_get(x_3, 2);
x_136 = lean_ctor_get(x_3, 3);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
x_137 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_137, 0, x_133);
lean_ctor_set(x_137, 1, x_134);
lean_ctor_set(x_137, 2, x_135);
lean_ctor_set(x_137, 3, x_136);
lean_ctor_set(x_137, 4, x_127);
x_138 = lean_unbox(x_128);
lean_ctor_set_uint8(x_137, sizeof(void*)*5, x_138);
x_139 = lean_unbox(x_128);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_140 = l_Lean_Meta_Simp_rewrite_x3f(x_2, x_129, x_130, x_131, x_139, x_137, x_4, x_5, x_6, x_7, x_8, x_9, x_126);
lean_dec(x_131);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
lean_inc(x_141);
x_143 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_143, 0, x_141);
x_144 = l_Lean_Elab_Tactic_NormCast_upwardAndElim___lam__0(x_5, x_132, x_143, x_142);
lean_dec(x_143);
lean_dec(x_5);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_172 = lean_box(0);
lean_inc(x_2);
x_173 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_173, 0, x_2);
lean_ctor_set(x_173, 1, x_172);
x_174 = lean_unbox(x_105);
lean_ctor_set_uint8(x_173, sizeof(void*)*2, x_174);
x_146 = x_173;
goto block_171;
}
else
{
lean_object* x_175; 
x_175 = lean_ctor_get(x_141, 0);
lean_inc(x_175);
lean_dec(x_141);
x_146 = x_175;
goto block_171;
}
block_171:
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_148 = l_Lean_Elab_Tactic_NormCast_splittingProcedure(x_147, x_6, x_7, x_8, x_9, x_145);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = l_Lean_Meta_Simp_Result_mkEqTrans(x_146, x_149, x_6, x_7, x_8, x_9, x_150);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_154 = x_151;
} else {
 lean_dec_ref(x_151);
 x_154 = lean_box(0);
}
x_155 = lean_ctor_get(x_152, 0);
lean_inc(x_155);
x_156 = lean_expr_eqv(x_155, x_2);
lean_dec(x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; 
lean_dec(x_2);
x_157 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_157, 0, x_152);
if (lean_is_scalar(x_154)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_154;
}
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_153);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_152);
x_159 = lean_box(0);
x_160 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_160, 0, x_2);
lean_ctor_set(x_160, 1, x_159);
lean_ctor_set_uint8(x_160, sizeof(void*)*2, x_156);
x_161 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_161, 0, x_160);
if (lean_is_scalar(x_154)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_154;
}
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_153);
return x_162;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_2);
x_163 = lean_ctor_get(x_151, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_151, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_165 = x_151;
} else {
 lean_dec_ref(x_151);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_164);
return x_166;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_146);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_167 = lean_ctor_get(x_148, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_148, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_169 = x_148;
} else {
 lean_dec_ref(x_148);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(1, 2, 0);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_167);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_176 = lean_ctor_get(x_140, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_140, 1);
lean_inc(x_177);
lean_dec(x_140);
x_178 = lean_box(0);
x_179 = l_Lean_Elab_Tactic_NormCast_upwardAndElim___lam__0(x_5, x_132, x_178, x_177);
lean_dec(x_5);
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_181 = x_179;
} else {
 lean_dec_ref(x_179);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_182 = x_181;
 lean_ctor_set_tag(x_182, 1);
}
lean_ctor_set(x_182, 0, x_176);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_upwardAndElim___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_NormCast_upwardAndElim___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_upwardAndElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_NormCast_upwardAndElim(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_numeralToCoe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_8 = lean_mk_string_unchecked("failed", 6, 6);
x_9 = l_Lean_stringToMessageData(x_8);
lean_dec(x_8);
x_10 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_9, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_13);
x_15 = lean_whnf(x_13, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_mk_string_unchecked("Nat", 3, 3);
lean_inc(x_18);
x_19 = l_Lean_Name_mkStr1(x_18);
x_20 = l_Lean_Expr_isConstOf(x_16, x_19);
lean_dec(x_19);
lean_dec(x_16);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_mk_string_unchecked("cast", 4, 4);
x_22 = l_Lean_Name_mkStr2(x_18, x_21);
lean_ctor_set(x_7, 0, x_13);
x_23 = lean_box(0);
x_24 = l_Lean_mkNatLit(x_14);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_unsigned_to_nat(3u);
x_27 = lean_mk_empty_array_with_capacity(x_26);
x_28 = lean_array_push(x_27, x_7);
x_29 = lean_array_push(x_28, x_23);
x_30 = lean_array_push(x_29, x_25);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_31 = l_Lean_Meta_mkAppOptM(x_22, x_30, x_2, x_3, x_4, x_5, x_17);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_34 = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(x_1, x_32, x_2, x_3, x_4, x_5, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_mk_string_unchecked("failed", 6, 6);
x_38 = l_Lean_stringToMessageData(x_37);
lean_dec(x_37);
x_39 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_38, x_2, x_3, x_4, x_5, x_36);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_39;
}
else
{
uint8_t x_40; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_34);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_34, 0);
lean_dec(x_41);
x_42 = lean_ctor_get(x_35, 0);
lean_inc(x_42);
lean_dec(x_35);
lean_ctor_set(x_34, 0, x_42);
return x_34;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_34, 1);
lean_inc(x_43);
lean_dec(x_34);
x_44 = lean_ctor_get(x_35, 0);
lean_inc(x_44);
lean_dec(x_35);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_34);
if (x_46 == 0)
{
return x_34;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_34, 0);
x_48 = lean_ctor_get(x_34, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_34);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_31);
if (x_50 == 0)
{
return x_31;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_31, 0);
x_52 = lean_ctor_get(x_31, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_31);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_free_object(x_7);
lean_dec(x_1);
x_54 = lean_mk_string_unchecked("failed", 6, 6);
x_55 = l_Lean_stringToMessageData(x_54);
lean_dec(x_54);
x_56 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_55, x_2, x_3, x_4, x_5, x_17);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
return x_56;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_56);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_14);
lean_dec(x_13);
lean_free_object(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_15);
if (x_61 == 0)
{
return x_15;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_15, 0);
x_63 = lean_ctor_get(x_15, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_15);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_7, 0);
lean_inc(x_65);
lean_dec(x_7);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_66);
x_68 = lean_whnf(x_66, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_mk_string_unchecked("Nat", 3, 3);
lean_inc(x_71);
x_72 = l_Lean_Name_mkStr1(x_71);
x_73 = l_Lean_Expr_isConstOf(x_69, x_72);
lean_dec(x_72);
lean_dec(x_69);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_74 = lean_mk_string_unchecked("cast", 4, 4);
x_75 = l_Lean_Name_mkStr2(x_71, x_74);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_66);
x_77 = lean_box(0);
x_78 = l_Lean_mkNatLit(x_67);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_80 = lean_unsigned_to_nat(3u);
x_81 = lean_mk_empty_array_with_capacity(x_80);
x_82 = lean_array_push(x_81, x_76);
x_83 = lean_array_push(x_82, x_77);
x_84 = lean_array_push(x_83, x_79);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_85 = l_Lean_Meta_mkAppOptM(x_75, x_84, x_2, x_3, x_4, x_5, x_70);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_88 = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(x_1, x_86, x_2, x_3, x_4, x_5, x_87);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_mk_string_unchecked("failed", 6, 6);
x_92 = l_Lean_stringToMessageData(x_91);
lean_dec(x_91);
x_93 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_92, x_2, x_3, x_4, x_5, x_90);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_94 = lean_ctor_get(x_88, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_95 = x_88;
} else {
 lean_dec_ref(x_88);
 x_95 = lean_box(0);
}
x_96 = lean_ctor_get(x_89, 0);
lean_inc(x_96);
lean_dec(x_89);
if (lean_is_scalar(x_95)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_95;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_94);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_98 = lean_ctor_get(x_88, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_88, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_100 = x_88;
} else {
 lean_dec_ref(x_88);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_102 = lean_ctor_get(x_85, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_85, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_104 = x_85;
} else {
 lean_dec_ref(x_85);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_71);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_1);
x_106 = lean_mk_string_unchecked("failed", 6, 6);
x_107 = l_Lean_stringToMessageData(x_106);
lean_dec(x_106);
x_108 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_107, x_2, x_3, x_4, x_5, x_70);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_111 = x_108;
} else {
 lean_dec_ref(x_108);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_113 = lean_ctor_get(x_68, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_68, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_115 = x_68;
} else {
 lean_dec_ref(x_68);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg____x40_Lean_Elab_Tactic_NormCast___hyg_6395_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Meta", 4, 4);
x_9 = lean_mk_string_unchecked("Simp", 4, 4);
x_10 = lean_mk_string_unchecked("NormCastConfig", 14, 14);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
x_14 = l_Lean_Meta_evalExpr_x27(lean_box(0), x_11, x_1, x_13, x_2, x_3, x_4, x_5, x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalUnsafe____x40_Lean_Elab_Tactic_NormCast___hyg_6395_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg____x40_Lean_Elab_Tactic_NormCast___hyg_6395_(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalUnsafe____x40_Lean_Elab_Tactic_NormCast___hyg_6395____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_NormCast_evalUnsafe____x40_Lean_Elab_Tactic_NormCast___hyg_6395_(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
lean_inc(x_1);
x_37 = l_Lean_Parser_Tactic_getConfigItems(x_1);
x_38 = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigItemViews(x_37);
x_39 = l_Array_isEmpty___redArg(x_38);
x_40 = lean_box(1);
if (x_39 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_st_ref_get(x_8, x_9);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_69; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
x_45 = lean_ctor_get(x_7, 5);
x_46 = l_Lean_replaceRef(x_1, x_45);
lean_dec(x_1);
x_47 = lean_ctor_get(x_7, 0);
x_48 = lean_ctor_get(x_7, 1);
x_49 = lean_ctor_get(x_7, 2);
x_50 = lean_ctor_get(x_7, 3);
x_51 = lean_ctor_get(x_7, 4);
x_52 = lean_ctor_get(x_7, 6);
x_53 = lean_ctor_get(x_7, 7);
x_54 = lean_ctor_get(x_7, 8);
x_55 = lean_ctor_get(x_7, 9);
x_56 = lean_ctor_get(x_7, 10);
x_57 = lean_ctor_get_uint8(x_7, sizeof(void*)*13);
x_58 = lean_ctor_get(x_7, 11);
x_59 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_60 = lean_ctor_get(x_7, 12);
lean_inc(x_60);
lean_inc(x_58);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
x_61 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_61, 0, x_47);
lean_ctor_set(x_61, 1, x_48);
lean_ctor_set(x_61, 2, x_49);
lean_ctor_set(x_61, 3, x_50);
lean_ctor_set(x_61, 4, x_51);
lean_ctor_set(x_61, 5, x_46);
lean_ctor_set(x_61, 6, x_52);
lean_ctor_set(x_61, 7, x_53);
lean_ctor_set(x_61, 8, x_54);
lean_ctor_set(x_61, 9, x_55);
lean_ctor_set(x_61, 10, x_56);
lean_ctor_set(x_61, 11, x_58);
lean_ctor_set(x_61, 12, x_60);
lean_ctor_set_uint8(x_61, sizeof(void*)*13, x_57);
lean_ctor_set_uint8(x_61, sizeof(void*)*13 + 1, x_59);
x_62 = lean_ctor_get(x_43, 0);
lean_inc(x_62);
lean_dec(x_43);
x_63 = lean_mk_string_unchecked("Lean", 4, 4);
x_64 = lean_mk_string_unchecked("Meta", 4, 4);
x_65 = lean_mk_string_unchecked("Simp", 4, 4);
x_66 = lean_mk_string_unchecked("NormCastConfig", 14, 14);
x_67 = l_Lean_Name_mkStr4(x_63, x_64, x_65, x_66);
x_68 = lean_unbox(x_40);
lean_inc(x_67);
x_69 = l_Lean_Environment_contains(x_62, x_67, x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec(x_38);
x_70 = lean_mk_string_unchecked("error evaluating configuration, environment does not yet contain type ", 70, 70);
x_71 = l_Lean_stringToMessageData(x_70);
lean_dec(x_70);
x_72 = l_Lean_MessageData_ofName(x_67);
lean_ctor_set_tag(x_41, 7);
lean_ctor_set(x_41, 1, x_72);
lean_ctor_set(x_41, 0, x_71);
x_73 = lean_mk_string_unchecked("", 0, 0);
x_74 = l_Lean_stringToMessageData(x_73);
lean_dec(x_73);
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_41);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_75, x_3, x_4, x_5, x_6, x_61, x_8, x_44);
lean_dec(x_8);
lean_dec(x_61);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
return x_76;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_76, 0);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_76);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
else
{
lean_object* x_81; 
lean_free_object(x_41);
lean_inc(x_8);
lean_inc(x_61);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_81 = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_elabConfig(x_36, x_67, x_38, x_3, x_4, x_5, x_6, x_61, x_8, x_44);
if (lean_obj_tag(x_81) == 0)
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_83 = lean_ctor_get(x_81, 0);
x_84 = lean_ctor_get(x_81, 1);
x_85 = l_Lean_Expr_hasSyntheticSorry(x_83);
if (x_85 == 0)
{
uint8_t x_86; 
lean_free_object(x_81);
x_86 = l_Lean_Expr_hasSorry(x_83);
if (x_86 == 0)
{
lean_object* x_87; 
lean_inc(x_8);
lean_inc(x_61);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_83);
x_87 = l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg____x40_Lean_Elab_Tactic_NormCast___hyg_6395_(x_83, x_5, x_6, x_61, x_8, x_84);
if (lean_obj_tag(x_87) == 0)
{
lean_dec(x_83);
lean_dec(x_61);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
x_90 = l_Lean_Exception_isInterrupt(x_88);
if (x_90 == 0)
{
uint8_t x_91; 
x_91 = l_Lean_Exception_isRuntime(x_88);
x_10 = x_8;
x_11 = x_3;
x_12 = x_88;
x_13 = x_4;
x_14 = x_89;
x_15 = x_61;
x_16 = x_87;
x_17 = x_5;
x_18 = x_83;
x_19 = x_6;
x_20 = x_91;
goto block_35;
}
else
{
x_10 = x_8;
x_11 = x_3;
x_12 = x_88;
x_13 = x_4;
x_14 = x_89;
x_15 = x_61;
x_16 = x_87;
x_17 = x_5;
x_18 = x_83;
x_19 = x_6;
x_20 = x_90;
goto block_35;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
lean_dec(x_83);
x_92 = lean_mk_string_unchecked("configuration contains 'sorry'", 30, 30);
x_93 = l_Lean_stringToMessageData(x_92);
lean_dec(x_92);
x_94 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_93, x_3, x_4, x_5, x_6, x_61, x_8, x_84);
lean_dec(x_8);
lean_dec(x_61);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
return x_94;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_94, 0);
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_94);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
lean_dec(x_83);
lean_dec(x_61);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_99 = lean_unsigned_to_nat(100000u);
x_100 = lean_unsigned_to_nat(2u);
x_101 = lean_box(0);
x_102 = lean_alloc_ctor(0, 2, 20);
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
lean_ctor_set_uint8(x_102, sizeof(void*)*2, x_39);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 1, x_85);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 2, x_39);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 3, x_39);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 4, x_39);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 5, x_39);
x_103 = lean_unbox(x_101);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 6, x_103);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 7, x_39);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 8, x_39);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 9, x_39);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 10, x_39);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 11, x_39);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 12, x_85);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 13, x_85);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 14, x_39);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 15, x_39);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 16, x_39);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 17, x_85);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 18, x_85);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 19, x_85);
lean_ctor_set(x_81, 0, x_102);
return x_81;
}
}
else
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_104 = lean_ctor_get(x_81, 0);
x_105 = lean_ctor_get(x_81, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_81);
x_106 = l_Lean_Expr_hasSyntheticSorry(x_104);
if (x_106 == 0)
{
uint8_t x_107; 
x_107 = l_Lean_Expr_hasSorry(x_104);
if (x_107 == 0)
{
lean_object* x_108; 
lean_inc(x_8);
lean_inc(x_61);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_104);
x_108 = l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg____x40_Lean_Elab_Tactic_NormCast___hyg_6395_(x_104, x_5, x_6, x_61, x_8, x_105);
if (lean_obj_tag(x_108) == 0)
{
lean_dec(x_104);
lean_dec(x_61);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
x_111 = l_Lean_Exception_isInterrupt(x_109);
if (x_111 == 0)
{
uint8_t x_112; 
x_112 = l_Lean_Exception_isRuntime(x_109);
x_10 = x_8;
x_11 = x_3;
x_12 = x_109;
x_13 = x_4;
x_14 = x_110;
x_15 = x_61;
x_16 = x_108;
x_17 = x_5;
x_18 = x_104;
x_19 = x_6;
x_20 = x_112;
goto block_35;
}
else
{
x_10 = x_8;
x_11 = x_3;
x_12 = x_109;
x_13 = x_4;
x_14 = x_110;
x_15 = x_61;
x_16 = x_108;
x_17 = x_5;
x_18 = x_104;
x_19 = x_6;
x_20 = x_111;
goto block_35;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_104);
x_113 = lean_mk_string_unchecked("configuration contains 'sorry'", 30, 30);
x_114 = l_Lean_stringToMessageData(x_113);
lean_dec(x_113);
x_115 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_114, x_3, x_4, x_5, x_6, x_61, x_8, x_105);
lean_dec(x_8);
lean_dec(x_61);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_118 = x_115;
} else {
 lean_dec_ref(x_115);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; 
lean_dec(x_104);
lean_dec(x_61);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_120 = lean_unsigned_to_nat(100000u);
x_121 = lean_unsigned_to_nat(2u);
x_122 = lean_box(0);
x_123 = lean_alloc_ctor(0, 2, 20);
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
lean_ctor_set_uint8(x_123, sizeof(void*)*2, x_39);
lean_ctor_set_uint8(x_123, sizeof(void*)*2 + 1, x_106);
lean_ctor_set_uint8(x_123, sizeof(void*)*2 + 2, x_39);
lean_ctor_set_uint8(x_123, sizeof(void*)*2 + 3, x_39);
lean_ctor_set_uint8(x_123, sizeof(void*)*2 + 4, x_39);
lean_ctor_set_uint8(x_123, sizeof(void*)*2 + 5, x_39);
x_124 = lean_unbox(x_122);
lean_ctor_set_uint8(x_123, sizeof(void*)*2 + 6, x_124);
lean_ctor_set_uint8(x_123, sizeof(void*)*2 + 7, x_39);
lean_ctor_set_uint8(x_123, sizeof(void*)*2 + 8, x_39);
lean_ctor_set_uint8(x_123, sizeof(void*)*2 + 9, x_39);
lean_ctor_set_uint8(x_123, sizeof(void*)*2 + 10, x_39);
lean_ctor_set_uint8(x_123, sizeof(void*)*2 + 11, x_39);
lean_ctor_set_uint8(x_123, sizeof(void*)*2 + 12, x_106);
lean_ctor_set_uint8(x_123, sizeof(void*)*2 + 13, x_106);
lean_ctor_set_uint8(x_123, sizeof(void*)*2 + 14, x_39);
lean_ctor_set_uint8(x_123, sizeof(void*)*2 + 15, x_39);
lean_ctor_set_uint8(x_123, sizeof(void*)*2 + 16, x_39);
lean_ctor_set_uint8(x_123, sizeof(void*)*2 + 17, x_106);
lean_ctor_set_uint8(x_123, sizeof(void*)*2 + 18, x_106);
lean_ctor_set_uint8(x_123, sizeof(void*)*2 + 19, x_106);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_105);
return x_125;
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_61);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_126 = !lean_is_exclusive(x_81);
if (x_126 == 0)
{
return x_81;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_81, 0);
x_128 = lean_ctor_get(x_81, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_81);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; uint8_t x_156; 
x_130 = lean_ctor_get(x_41, 0);
x_131 = lean_ctor_get(x_41, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_41);
x_132 = lean_ctor_get(x_7, 5);
x_133 = l_Lean_replaceRef(x_1, x_132);
lean_dec(x_1);
x_134 = lean_ctor_get(x_7, 0);
x_135 = lean_ctor_get(x_7, 1);
x_136 = lean_ctor_get(x_7, 2);
x_137 = lean_ctor_get(x_7, 3);
x_138 = lean_ctor_get(x_7, 4);
x_139 = lean_ctor_get(x_7, 6);
x_140 = lean_ctor_get(x_7, 7);
x_141 = lean_ctor_get(x_7, 8);
x_142 = lean_ctor_get(x_7, 9);
x_143 = lean_ctor_get(x_7, 10);
x_144 = lean_ctor_get_uint8(x_7, sizeof(void*)*13);
x_145 = lean_ctor_get(x_7, 11);
x_146 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_147 = lean_ctor_get(x_7, 12);
lean_inc(x_147);
lean_inc(x_145);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
x_148 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_148, 0, x_134);
lean_ctor_set(x_148, 1, x_135);
lean_ctor_set(x_148, 2, x_136);
lean_ctor_set(x_148, 3, x_137);
lean_ctor_set(x_148, 4, x_138);
lean_ctor_set(x_148, 5, x_133);
lean_ctor_set(x_148, 6, x_139);
lean_ctor_set(x_148, 7, x_140);
lean_ctor_set(x_148, 8, x_141);
lean_ctor_set(x_148, 9, x_142);
lean_ctor_set(x_148, 10, x_143);
lean_ctor_set(x_148, 11, x_145);
lean_ctor_set(x_148, 12, x_147);
lean_ctor_set_uint8(x_148, sizeof(void*)*13, x_144);
lean_ctor_set_uint8(x_148, sizeof(void*)*13 + 1, x_146);
x_149 = lean_ctor_get(x_130, 0);
lean_inc(x_149);
lean_dec(x_130);
x_150 = lean_mk_string_unchecked("Lean", 4, 4);
x_151 = lean_mk_string_unchecked("Meta", 4, 4);
x_152 = lean_mk_string_unchecked("Simp", 4, 4);
x_153 = lean_mk_string_unchecked("NormCastConfig", 14, 14);
x_154 = l_Lean_Name_mkStr4(x_150, x_151, x_152, x_153);
x_155 = lean_unbox(x_40);
lean_inc(x_154);
x_156 = l_Lean_Environment_contains(x_149, x_154, x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_38);
x_157 = lean_mk_string_unchecked("error evaluating configuration, environment does not yet contain type ", 70, 70);
x_158 = l_Lean_stringToMessageData(x_157);
lean_dec(x_157);
x_159 = l_Lean_MessageData_ofName(x_154);
x_160 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_mk_string_unchecked("", 0, 0);
x_162 = l_Lean_stringToMessageData(x_161);
lean_dec(x_161);
x_163 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_163, 0, x_160);
lean_ctor_set(x_163, 1, x_162);
x_164 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_163, x_3, x_4, x_5, x_6, x_148, x_8, x_131);
lean_dec(x_8);
lean_dec(x_148);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_167 = x_164;
} else {
 lean_dec_ref(x_164);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_166);
return x_168;
}
else
{
lean_object* x_169; 
lean_inc(x_8);
lean_inc(x_148);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_169 = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_elabConfig(x_36, x_154, x_38, x_3, x_4, x_5, x_6, x_148, x_8, x_131);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_172 = x_169;
} else {
 lean_dec_ref(x_169);
 x_172 = lean_box(0);
}
x_173 = l_Lean_Expr_hasSyntheticSorry(x_170);
if (x_173 == 0)
{
uint8_t x_174; 
lean_dec(x_172);
x_174 = l_Lean_Expr_hasSorry(x_170);
if (x_174 == 0)
{
lean_object* x_175; 
lean_inc(x_8);
lean_inc(x_148);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_170);
x_175 = l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg____x40_Lean_Elab_Tactic_NormCast___hyg_6395_(x_170, x_5, x_6, x_148, x_8, x_171);
if (lean_obj_tag(x_175) == 0)
{
lean_dec(x_170);
lean_dec(x_148);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_175;
}
else
{
lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
x_178 = l_Lean_Exception_isInterrupt(x_176);
if (x_178 == 0)
{
uint8_t x_179; 
x_179 = l_Lean_Exception_isRuntime(x_176);
x_10 = x_8;
x_11 = x_3;
x_12 = x_176;
x_13 = x_4;
x_14 = x_177;
x_15 = x_148;
x_16 = x_175;
x_17 = x_5;
x_18 = x_170;
x_19 = x_6;
x_20 = x_179;
goto block_35;
}
else
{
x_10 = x_8;
x_11 = x_3;
x_12 = x_176;
x_13 = x_4;
x_14 = x_177;
x_15 = x_148;
x_16 = x_175;
x_17 = x_5;
x_18 = x_170;
x_19 = x_6;
x_20 = x_178;
goto block_35;
}
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_170);
x_180 = lean_mk_string_unchecked("configuration contains 'sorry'", 30, 30);
x_181 = l_Lean_stringToMessageData(x_180);
lean_dec(x_180);
x_182 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_181, x_3, x_4, x_5, x_6, x_148, x_8, x_171);
lean_dec(x_8);
lean_dec(x_148);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_185 = x_182;
} else {
 lean_dec_ref(x_182);
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
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; lean_object* x_192; 
lean_dec(x_170);
lean_dec(x_148);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_187 = lean_unsigned_to_nat(100000u);
x_188 = lean_unsigned_to_nat(2u);
x_189 = lean_box(0);
x_190 = lean_alloc_ctor(0, 2, 20);
lean_ctor_set(x_190, 0, x_187);
lean_ctor_set(x_190, 1, x_188);
lean_ctor_set_uint8(x_190, sizeof(void*)*2, x_39);
lean_ctor_set_uint8(x_190, sizeof(void*)*2 + 1, x_173);
lean_ctor_set_uint8(x_190, sizeof(void*)*2 + 2, x_39);
lean_ctor_set_uint8(x_190, sizeof(void*)*2 + 3, x_39);
lean_ctor_set_uint8(x_190, sizeof(void*)*2 + 4, x_39);
lean_ctor_set_uint8(x_190, sizeof(void*)*2 + 5, x_39);
x_191 = lean_unbox(x_189);
lean_ctor_set_uint8(x_190, sizeof(void*)*2 + 6, x_191);
lean_ctor_set_uint8(x_190, sizeof(void*)*2 + 7, x_39);
lean_ctor_set_uint8(x_190, sizeof(void*)*2 + 8, x_39);
lean_ctor_set_uint8(x_190, sizeof(void*)*2 + 9, x_39);
lean_ctor_set_uint8(x_190, sizeof(void*)*2 + 10, x_39);
lean_ctor_set_uint8(x_190, sizeof(void*)*2 + 11, x_39);
lean_ctor_set_uint8(x_190, sizeof(void*)*2 + 12, x_173);
lean_ctor_set_uint8(x_190, sizeof(void*)*2 + 13, x_173);
lean_ctor_set_uint8(x_190, sizeof(void*)*2 + 14, x_39);
lean_ctor_set_uint8(x_190, sizeof(void*)*2 + 15, x_39);
lean_ctor_set_uint8(x_190, sizeof(void*)*2 + 16, x_39);
lean_ctor_set_uint8(x_190, sizeof(void*)*2 + 17, x_173);
lean_ctor_set_uint8(x_190, sizeof(void*)*2 + 18, x_173);
lean_ctor_set_uint8(x_190, sizeof(void*)*2 + 19, x_173);
if (lean_is_scalar(x_172)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_172;
}
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_171);
return x_192;
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_148);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_193 = lean_ctor_get(x_169, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_169, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_195 = x_169;
} else {
 lean_dec_ref(x_169);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(1, 2, 0);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_193);
lean_ctor_set(x_196, 1, x_194);
return x_196;
}
}
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; uint8_t x_203; uint8_t x_204; uint8_t x_205; uint8_t x_206; uint8_t x_207; uint8_t x_208; uint8_t x_209; uint8_t x_210; uint8_t x_211; uint8_t x_212; uint8_t x_213; uint8_t x_214; uint8_t x_215; uint8_t x_216; uint8_t x_217; uint8_t x_218; uint8_t x_219; uint8_t x_220; uint8_t x_221; lean_object* x_222; 
lean_dec(x_38);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_197 = lean_unsigned_to_nat(100000u);
x_198 = lean_unsigned_to_nat(2u);
x_199 = lean_box(0);
x_200 = lean_box(0);
x_201 = lean_alloc_ctor(0, 2, 20);
lean_ctor_set(x_201, 0, x_197);
lean_ctor_set(x_201, 1, x_198);
x_202 = lean_unbox(x_199);
lean_ctor_set_uint8(x_201, sizeof(void*)*2, x_202);
x_203 = lean_unbox(x_40);
lean_ctor_set_uint8(x_201, sizeof(void*)*2 + 1, x_203);
x_204 = lean_unbox(x_199);
lean_ctor_set_uint8(x_201, sizeof(void*)*2 + 2, x_204);
x_205 = lean_unbox(x_199);
lean_ctor_set_uint8(x_201, sizeof(void*)*2 + 3, x_205);
x_206 = lean_unbox(x_199);
lean_ctor_set_uint8(x_201, sizeof(void*)*2 + 4, x_206);
x_207 = lean_unbox(x_199);
lean_ctor_set_uint8(x_201, sizeof(void*)*2 + 5, x_207);
x_208 = lean_unbox(x_200);
lean_ctor_set_uint8(x_201, sizeof(void*)*2 + 6, x_208);
x_209 = lean_unbox(x_199);
lean_ctor_set_uint8(x_201, sizeof(void*)*2 + 7, x_209);
x_210 = lean_unbox(x_199);
lean_ctor_set_uint8(x_201, sizeof(void*)*2 + 8, x_210);
x_211 = lean_unbox(x_199);
lean_ctor_set_uint8(x_201, sizeof(void*)*2 + 9, x_211);
x_212 = lean_unbox(x_199);
lean_ctor_set_uint8(x_201, sizeof(void*)*2 + 10, x_212);
x_213 = lean_unbox(x_199);
lean_ctor_set_uint8(x_201, sizeof(void*)*2 + 11, x_213);
x_214 = lean_unbox(x_40);
lean_ctor_set_uint8(x_201, sizeof(void*)*2 + 12, x_214);
x_215 = lean_unbox(x_40);
lean_ctor_set_uint8(x_201, sizeof(void*)*2 + 13, x_215);
x_216 = lean_unbox(x_199);
lean_ctor_set_uint8(x_201, sizeof(void*)*2 + 14, x_216);
x_217 = lean_unbox(x_199);
lean_ctor_set_uint8(x_201, sizeof(void*)*2 + 15, x_217);
x_218 = lean_unbox(x_199);
lean_ctor_set_uint8(x_201, sizeof(void*)*2 + 16, x_218);
x_219 = lean_unbox(x_40);
lean_ctor_set_uint8(x_201, sizeof(void*)*2 + 17, x_219);
x_220 = lean_unbox(x_40);
lean_ctor_set_uint8(x_201, sizeof(void*)*2 + 18, x_220);
x_221 = lean_unbox(x_40);
lean_ctor_set_uint8(x_201, sizeof(void*)*2 + 19, x_221);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_201);
lean_ctor_set(x_222, 1, x_9);
return x_222;
}
block_35:
{
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_16);
x_21 = lean_mk_string_unchecked("error evaluating configuration\n", 31, 31);
x_22 = l_Lean_stringToMessageData(x_21);
lean_dec(x_21);
x_23 = l_Lean_MessageData_ofExpr(x_18);
x_24 = l_Lean_indentD(x_23);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_mk_string_unchecked("\n\nException: ", 13, 13);
x_27 = l_Lean_stringToMessageData(x_26);
lean_dec(x_26);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Exception_toMessageData(x_12);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_mk_string_unchecked("", 0, 0);
x_32 = l_Lean_stringToMessageData(x_31);
lean_dec(x_31);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_33, x_11, x_13, x_17, x_19, x_15, x_10, x_14);
lean_dec(x_10);
lean_dec(x_15);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
return x_34;
}
else
{
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabNormCastConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_NormCast_elabNormCastConfig(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_mk_string_unchecked("", 0, 0);
x_9 = l_Lean_stringToMessageData(x_8);
lean_dec(x_8);
x_10 = l_Lean_MessageData_ofExpr(x_1);
lean_inc(x_9);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
x_8 = lean_mk_string_unchecked("", 0, 0);
x_9 = l_Lean_stringToMessageData(x_8);
lean_dec(x_8);
x_10 = lean_mk_string_unchecked("💥️", 7, 2);
x_11 = l_Lean_stringToMessageData(x_10);
lean_dec(x_10);
lean_inc(x_9);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_mk_string_unchecked(" ", 1, 1);
x_14 = l_Lean_stringToMessageData(x_13);
lean_dec(x_13);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_stringToMessageData(x_1);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_7);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
lean_dec(x_2);
x_21 = lean_mk_string_unchecked("", 0, 0);
x_22 = l_Lean_stringToMessageData(x_21);
lean_dec(x_21);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
x_24 = l_Lean_MessageData_ofExpr(x_23);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_mk_string_unchecked(" (after ", 8, 8);
x_27 = l_Lean_stringToMessageData(x_26);
lean_dec(x_26);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_stringToMessageData(x_1);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_mk_string_unchecked(")", 1, 1);
x_32 = l_Lean_stringToMessageData(x_31);
lean_dec(x_31);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_7);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__6(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__4___boxed), 7, 1);
lean_closure_set(x_10, 0, x_3);
x_11 = lean_mk_string_unchecked("", 0, 0);
x_12 = l_Lean_withTraceNode___at___Lean_Meta_processPostponed_spec__0(lean_box(0), x_1, x_10, x_4, x_2, x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__7(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_17; lean_object* x_25; 
lean_inc(x_3);
x_25 = l_Lean_Elab_Tactic_NormCast_numeralToCoe(x_3, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_25) == 0)
{
lean_dec(x_3);
lean_dec(x_1);
x_17 = x_25;
goto block_24;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_31; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
x_31 = l_Lean_Exception_isInterrupt(x_26);
if (x_31 == 0)
{
uint8_t x_32; 
x_32 = l_Lean_Exception_isRuntime(x_26);
lean_dec(x_26);
x_28 = x_32;
goto block_30;
}
else
{
lean_dec(x_26);
x_28 = x_31;
goto block_30;
}
block_30:
{
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_29, 0, x_3);
lean_ctor_set(x_29, 1, x_1);
lean_ctor_set_uint8(x_29, sizeof(void*)*2, x_2);
x_12 = x_29;
x_13 = x_27;
goto block_16;
}
else
{
lean_dec(x_27);
lean_dec(x_3);
lean_dec(x_1);
x_17 = x_25;
goto block_24;
}
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
block_24:
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_12 = x_18;
x_13 = x_19;
goto block_16;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Meta_Simp_mkContext(x_1, x_2, x_3, x_12, x_13, x_14, x_15, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; lean_object* x_28; lean_object* x_29; size_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_21);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_unsigned_to_nat(0u);
lean_inc(x_22);
lean_ctor_set(x_17, 1, x_23);
lean_ctor_set(x_17, 0, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_21);
x_25 = lean_unsigned_to_nat(2u);
x_26 = lean_unsigned_to_nat(5u);
x_27 = lean_usize_of_nat(x_26);
x_28 = lean_usize_to_nat(x_27);
x_29 = lean_nat_pow(x_25, x_28);
lean_dec(x_28);
x_30 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_31 = lean_usize_to_nat(x_30);
x_32 = lean_mk_empty_array_with_capacity(x_31);
lean_dec(x_31);
lean_inc(x_32);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_23);
lean_ctor_set(x_34, 3, x_23);
lean_ctor_set_usize(x_34, 4, x_27);
lean_inc(x_22);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_22);
lean_ctor_set(x_35, 1, x_22);
lean_ctor_set(x_35, 2, x_24);
lean_ctor_set(x_35, 3, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_17);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_37, 0, x_4);
lean_ctor_set(x_37, 1, x_5);
lean_ctor_set(x_37, 2, x_6);
lean_ctor_set(x_37, 3, x_7);
lean_ctor_set(x_37, 4, x_8);
lean_ctor_set_uint8(x_37, sizeof(void*)*5, x_9);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_38 = l_Lean_Meta_Simp_main(x_10, x_19, x_36, x_37, x_12, x_13, x_14, x_15, x_20);
lean_dec(x_36);
lean_dec(x_19);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Meta_Simp_Result_mkEqTrans(x_11, x_41, x_12, x_13, x_14, x_15, x_40);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_43 = !lean_is_exclusive(x_38);
if (x_43 == 0)
{
return x_38;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_38, 0);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_38);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; size_t x_56; lean_object* x_57; lean_object* x_58; size_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_47 = lean_ctor_get(x_17, 0);
x_48 = lean_ctor_get(x_17, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_17);
x_49 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_49);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_unsigned_to_nat(0u);
lean_inc(x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_49);
x_54 = lean_unsigned_to_nat(2u);
x_55 = lean_unsigned_to_nat(5u);
x_56 = lean_usize_of_nat(x_55);
x_57 = lean_usize_to_nat(x_56);
x_58 = lean_nat_pow(x_54, x_57);
lean_dec(x_57);
x_59 = lean_usize_of_nat(x_58);
lean_dec(x_58);
x_60 = lean_usize_to_nat(x_59);
x_61 = lean_mk_empty_array_with_capacity(x_60);
lean_dec(x_60);
lean_inc(x_61);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
lean_ctor_set(x_63, 2, x_51);
lean_ctor_set(x_63, 3, x_51);
lean_ctor_set_usize(x_63, 4, x_56);
lean_inc(x_50);
x_64 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_64, 0, x_50);
lean_ctor_set(x_64, 1, x_50);
lean_ctor_set(x_64, 2, x_53);
lean_ctor_set(x_64, 3, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_52);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_66, 0, x_4);
lean_ctor_set(x_66, 1, x_5);
lean_ctor_set(x_66, 2, x_6);
lean_ctor_set(x_66, 3, x_7);
lean_ctor_set(x_66, 4, x_8);
lean_ctor_set_uint8(x_66, sizeof(void*)*5, x_9);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_67 = l_Lean_Meta_Simp_main(x_10, x_47, x_65, x_66, x_12, x_13, x_14, x_15, x_48);
lean_dec(x_65);
lean_dec(x_47);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_Meta_Simp_Result_mkEqTrans(x_11, x_70, x_12, x_13, x_14, x_15, x_69);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_72 = lean_ctor_get(x_67, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_67, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_74 = x_67;
} else {
 lean_dec_ref(x_67);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Meta_SimpExtension_getTheorems___redArg(x_1, x_14, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = l_Lean_Meta_Simp_mkContext(x_2, x_3, x_4, x_11, x_12, x_13, x_14, x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; lean_object* x_33; lean_object* x_34; size_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_upwardAndElim___boxed), 10, 1);
lean_closure_set(x_24, 0, x_18);
x_25 = lean_ctor_get(x_5, 0);
lean_inc(x_25);
x_26 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_26);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_unsigned_to_nat(0u);
lean_inc(x_27);
lean_ctor_set(x_20, 1, x_28);
lean_ctor_set(x_20, 0, x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_26);
x_30 = lean_unsigned_to_nat(2u);
x_31 = lean_unsigned_to_nat(5u);
x_32 = lean_usize_of_nat(x_31);
x_33 = lean_usize_to_nat(x_32);
x_34 = lean_nat_pow(x_30, x_33);
lean_dec(x_33);
x_35 = lean_usize_of_nat(x_34);
lean_dec(x_34);
x_36 = lean_usize_to_nat(x_35);
x_37 = lean_mk_empty_array_with_capacity(x_36);
lean_dec(x_36);
lean_inc(x_37);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set(x_39, 2, x_28);
lean_ctor_set(x_39, 3, x_28);
lean_ctor_set_usize(x_39, 4, x_32);
lean_inc(x_27);
x_40 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_40, 0, x_27);
lean_ctor_set(x_40, 1, x_27);
lean_ctor_set(x_40, 2, x_29);
lean_ctor_set(x_40, 3, x_39);
lean_ctor_set(x_16, 1, x_40);
lean_ctor_set(x_16, 0, x_20);
x_41 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_41, 0, x_6);
lean_ctor_set(x_41, 1, x_24);
lean_ctor_set(x_41, 2, x_7);
lean_ctor_set(x_41, 3, x_8);
lean_ctor_set(x_41, 4, x_9);
lean_ctor_set_uint8(x_41, sizeof(void*)*5, x_10);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_42 = l_Lean_Meta_Simp_main(x_25, x_22, x_16, x_41, x_11, x_12, x_13, x_14, x_23);
lean_dec(x_16);
lean_dec(x_22);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Meta_Simp_Result_mkEqTrans(x_5, x_45, x_11, x_12, x_13, x_14, x_44);
return x_46;
}
else
{
uint8_t x_47; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
x_47 = !lean_is_exclusive(x_42);
if (x_47 == 0)
{
return x_42;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_42, 0);
x_49 = lean_ctor_get(x_42, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_42);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; size_t x_62; lean_object* x_63; lean_object* x_64; size_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_51 = lean_ctor_get(x_20, 0);
x_52 = lean_ctor_get(x_20, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_20);
x_53 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_upwardAndElim___boxed), 10, 1);
lean_closure_set(x_53, 0, x_18);
x_54 = lean_ctor_get(x_5, 0);
lean_inc(x_54);
x_55 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_55);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_unsigned_to_nat(0u);
lean_inc(x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_55);
x_60 = lean_unsigned_to_nat(2u);
x_61 = lean_unsigned_to_nat(5u);
x_62 = lean_usize_of_nat(x_61);
x_63 = lean_usize_to_nat(x_62);
x_64 = lean_nat_pow(x_60, x_63);
lean_dec(x_63);
x_65 = lean_usize_of_nat(x_64);
lean_dec(x_64);
x_66 = lean_usize_to_nat(x_65);
x_67 = lean_mk_empty_array_with_capacity(x_66);
lean_dec(x_66);
lean_inc(x_67);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
lean_ctor_set(x_69, 2, x_57);
lean_ctor_set(x_69, 3, x_57);
lean_ctor_set_usize(x_69, 4, x_62);
lean_inc(x_56);
x_70 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_70, 0, x_56);
lean_ctor_set(x_70, 1, x_56);
lean_ctor_set(x_70, 2, x_59);
lean_ctor_set(x_70, 3, x_69);
lean_ctor_set(x_16, 1, x_70);
lean_ctor_set(x_16, 0, x_58);
x_71 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_71, 0, x_6);
lean_ctor_set(x_71, 1, x_53);
lean_ctor_set(x_71, 2, x_7);
lean_ctor_set(x_71, 3, x_8);
lean_ctor_set(x_71, 4, x_9);
lean_ctor_set_uint8(x_71, sizeof(void*)*5, x_10);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_72 = l_Lean_Meta_Simp_main(x_54, x_51, x_16, x_71, x_11, x_12, x_13, x_14, x_52);
lean_dec(x_16);
lean_dec(x_51);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lean_Meta_Simp_Result_mkEqTrans(x_5, x_75, x_11, x_12, x_13, x_14, x_74);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
x_77 = lean_ctor_get(x_72, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_72, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_79 = x_72;
} else {
 lean_dec_ref(x_72);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; size_t x_96; lean_object* x_97; lean_object* x_98; size_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_81 = lean_ctor_get(x_16, 0);
x_82 = lean_ctor_get(x_16, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_16);
x_83 = l_Lean_Meta_Simp_mkContext(x_2, x_3, x_4, x_11, x_12, x_13, x_14, x_82);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_86 = x_83;
} else {
 lean_dec_ref(x_83);
 x_86 = lean_box(0);
}
x_87 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_upwardAndElim___boxed), 10, 1);
lean_closure_set(x_87, 0, x_81);
x_88 = lean_ctor_get(x_5, 0);
lean_inc(x_88);
x_89 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_89);
x_90 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_91 = lean_unsigned_to_nat(0u);
lean_inc(x_90);
if (lean_is_scalar(x_86)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_86;
}
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_93, 0, x_89);
x_94 = lean_unsigned_to_nat(2u);
x_95 = lean_unsigned_to_nat(5u);
x_96 = lean_usize_of_nat(x_95);
x_97 = lean_usize_to_nat(x_96);
x_98 = lean_nat_pow(x_94, x_97);
lean_dec(x_97);
x_99 = lean_usize_of_nat(x_98);
lean_dec(x_98);
x_100 = lean_usize_to_nat(x_99);
x_101 = lean_mk_empty_array_with_capacity(x_100);
lean_dec(x_100);
lean_inc(x_101);
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_103 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_101);
lean_ctor_set(x_103, 2, x_91);
lean_ctor_set(x_103, 3, x_91);
lean_ctor_set_usize(x_103, 4, x_96);
lean_inc(x_90);
x_104 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_104, 0, x_90);
lean_ctor_set(x_104, 1, x_90);
lean_ctor_set(x_104, 2, x_93);
lean_ctor_set(x_104, 3, x_103);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_92);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_106, 0, x_6);
lean_ctor_set(x_106, 1, x_87);
lean_ctor_set(x_106, 2, x_7);
lean_ctor_set(x_106, 3, x_8);
lean_ctor_set(x_106, 4, x_9);
lean_ctor_set_uint8(x_106, sizeof(void*)*5, x_10);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_107 = l_Lean_Meta_Simp_main(x_88, x_84, x_105, x_106, x_11, x_12, x_13, x_14, x_85);
lean_dec(x_105);
lean_dec(x_84);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
lean_dec(x_108);
x_111 = l_Lean_Meta_Simp_Result_mkEqTrans(x_5, x_110, x_11, x_12, x_13, x_14, x_109);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
x_112 = lean_ctor_get(x_107, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_107, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_114 = x_107;
} else {
 lean_dec_ref(x_107);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Meta_SimpExtension_getTheorems___redArg(x_1, x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_mk_empty_array_with_capacity(x_15);
x_17 = lean_array_push(x_16, x_13);
x_18 = l_Lean_Meta_Simp_mkContext(x_2, x_17, x_3, x_6, x_7, x_8, x_9, x_14);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; lean_object* x_31; lean_object* x_32; size_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_ctor_get(x_4, 0);
lean_inc(x_22);
x_23 = lean_box(0);
x_24 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_24);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_unsigned_to_nat(0u);
lean_inc(x_25);
lean_ctor_set(x_18, 1, x_26);
lean_ctor_set(x_18, 0, x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_24);
x_28 = lean_unsigned_to_nat(2u);
x_29 = lean_unsigned_to_nat(5u);
x_30 = lean_usize_of_nat(x_29);
x_31 = lean_usize_to_nat(x_30);
x_32 = lean_nat_pow(x_28, x_31);
lean_dec(x_31);
x_33 = lean_usize_of_nat(x_32);
lean_dec(x_32);
x_34 = lean_usize_to_nat(x_33);
x_35 = lean_mk_empty_array_with_capacity(x_34);
lean_dec(x_34);
lean_inc(x_35);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set(x_37, 2, x_26);
lean_ctor_set(x_37, 3, x_26);
lean_ctor_set_usize(x_37, 4, x_30);
lean_inc(x_25);
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_25);
lean_ctor_set(x_38, 1, x_25);
lean_ctor_set(x_38, 2, x_27);
lean_ctor_set(x_38, 3, x_37);
lean_ctor_set(x_11, 1, x_38);
lean_ctor_set(x_11, 0, x_18);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_39 = l_Lean_Meta_simp(x_22, x_20, x_5, x_23, x_11, x_6, x_7, x_8, x_9, x_21);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Meta_Simp_Result_mkEqTrans(x_4, x_42, x_6, x_7, x_8, x_9, x_41);
return x_43;
}
else
{
uint8_t x_44; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_39);
if (x_44 == 0)
{
return x_39;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_39, 0);
x_46 = lean_ctor_get(x_39, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_39);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; size_t x_59; lean_object* x_60; lean_object* x_61; size_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_48 = lean_ctor_get(x_18, 0);
x_49 = lean_ctor_get(x_18, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_18);
x_50 = lean_ctor_get(x_4, 0);
lean_inc(x_50);
x_51 = lean_box(0);
x_52 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_52);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_unsigned_to_nat(0u);
lean_inc(x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_52);
x_57 = lean_unsigned_to_nat(2u);
x_58 = lean_unsigned_to_nat(5u);
x_59 = lean_usize_of_nat(x_58);
x_60 = lean_usize_to_nat(x_59);
x_61 = lean_nat_pow(x_57, x_60);
lean_dec(x_60);
x_62 = lean_usize_of_nat(x_61);
lean_dec(x_61);
x_63 = lean_usize_to_nat(x_62);
x_64 = lean_mk_empty_array_with_capacity(x_63);
lean_dec(x_63);
lean_inc(x_64);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
lean_ctor_set(x_66, 2, x_54);
lean_ctor_set(x_66, 3, x_54);
lean_ctor_set_usize(x_66, 4, x_59);
lean_inc(x_53);
x_67 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_67, 0, x_53);
lean_ctor_set(x_67, 1, x_53);
lean_ctor_set(x_67, 2, x_56);
lean_ctor_set(x_67, 3, x_66);
lean_ctor_set(x_11, 1, x_67);
lean_ctor_set(x_11, 0, x_55);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_68 = l_Lean_Meta_simp(x_50, x_48, x_5, x_51, x_11, x_6, x_7, x_8, x_9, x_49);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Lean_Meta_Simp_Result_mkEqTrans(x_4, x_71, x_6, x_7, x_8, x_9, x_70);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_73 = lean_ctor_get(x_68, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_68, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_75 = x_68;
} else {
 lean_dec_ref(x_68);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; size_t x_95; lean_object* x_96; lean_object* x_97; size_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_77 = lean_ctor_get(x_11, 0);
x_78 = lean_ctor_get(x_11, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_11);
x_79 = lean_unsigned_to_nat(1u);
x_80 = lean_mk_empty_array_with_capacity(x_79);
x_81 = lean_array_push(x_80, x_77);
x_82 = l_Lean_Meta_Simp_mkContext(x_2, x_81, x_3, x_6, x_7, x_8, x_9, x_78);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_85 = x_82;
} else {
 lean_dec_ref(x_82);
 x_85 = lean_box(0);
}
x_86 = lean_ctor_get(x_4, 0);
lean_inc(x_86);
x_87 = lean_box(0);
x_88 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_88);
x_89 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = lean_unsigned_to_nat(0u);
lean_inc(x_89);
if (lean_is_scalar(x_85)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_85;
}
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_92, 0, x_88);
x_93 = lean_unsigned_to_nat(2u);
x_94 = lean_unsigned_to_nat(5u);
x_95 = lean_usize_of_nat(x_94);
x_96 = lean_usize_to_nat(x_95);
x_97 = lean_nat_pow(x_93, x_96);
lean_dec(x_96);
x_98 = lean_usize_of_nat(x_97);
lean_dec(x_97);
x_99 = lean_usize_to_nat(x_98);
x_100 = lean_mk_empty_array_with_capacity(x_99);
lean_dec(x_99);
lean_inc(x_100);
x_101 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_102 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
lean_ctor_set(x_102, 2, x_90);
lean_ctor_set(x_102, 3, x_90);
lean_ctor_set_usize(x_102, 4, x_95);
lean_inc(x_89);
x_103 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_103, 0, x_89);
lean_ctor_set(x_103, 1, x_89);
lean_ctor_set(x_103, 2, x_92);
lean_ctor_set(x_103, 3, x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_91);
lean_ctor_set(x_104, 1, x_103);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_105 = l_Lean_Meta_simp(x_86, x_83, x_5, x_87, x_104, x_6, x_7, x_8, x_9, x_84);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_108);
lean_dec(x_106);
x_109 = l_Lean_Meta_Simp_Result_mkEqTrans(x_4, x_108, x_6, x_7, x_8, x_9, x_107);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_110 = lean_ctor_get(x_105, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_105, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_112 = x_105;
} else {
 lean_dec_ref(x_105);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_13 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_1, x_9, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_getSimpCongrTheorems(x_10, x_11, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__5___boxed), 10, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__3___boxed), 10, 1);
lean_closure_set(x_21, 0, x_19);
x_22 = lean_box(1);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__7___boxed), 11, 2);
lean_closure_set(x_23, 0, x_19);
lean_closure_set(x_23, 1, x_22);
lean_inc(x_14);
x_24 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_19);
x_25 = lean_unbox(x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*2, x_25);
x_26 = lean_mk_string_unchecked("pre-processing numerals", 23, 23);
x_27 = l_Array_empty(lean_box(0));
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_17);
lean_inc(x_27);
lean_inc(x_3);
x_28 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__8___boxed), 16, 11);
lean_closure_set(x_28, 0, x_3);
lean_closure_set(x_28, 1, x_27);
lean_closure_set(x_28, 2, x_17);
lean_closure_set(x_28, 3, x_4);
lean_closure_set(x_28, 4, x_23);
lean_closure_set(x_28, 5, x_20);
lean_closure_set(x_28, 6, x_5);
lean_closure_set(x_28, 7, x_21);
lean_closure_set(x_28, 8, x_22);
lean_closure_set(x_28, 9, x_14);
lean_closure_set(x_28, 10, x_24);
x_29 = lean_unbox(x_22);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_30 = l_Lean_Elab_Tactic_NormCast_derive___lam__6(x_2, x_29, x_26, x_28, x_8, x_9, x_10, x_11, x_18);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_mk_string_unchecked("moving upward, splitting and eliminating", 40, 40);
x_34 = l_Lean_Meta_NormCast_normCastExt;
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_inc(x_17);
lean_inc(x_27);
lean_inc(x_3);
x_36 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__11___boxed), 15, 10);
lean_closure_set(x_36, 0, x_35);
lean_closure_set(x_36, 1, x_3);
lean_closure_set(x_36, 2, x_27);
lean_closure_set(x_36, 3, x_17);
lean_closure_set(x_36, 4, x_31);
lean_closure_set(x_36, 5, x_6);
lean_closure_set(x_36, 6, x_20);
lean_closure_set(x_36, 7, x_7);
lean_closure_set(x_36, 8, x_21);
lean_closure_set(x_36, 9, x_22);
x_37 = lean_unbox(x_22);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_38 = l_Lean_Elab_Tactic_NormCast_derive___lam__6(x_2, x_37, x_33, x_36, x_8, x_9, x_10, x_11, x_32);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_mk_string_unchecked("reduceCtorEq", 12, 12);
x_42 = l_Lean_Name_mkStr1(x_41);
x_43 = lean_box(0);
x_44 = lean_unbox(x_43);
x_45 = l_Lean_Meta_Simp_SimprocsArray_add(x_27, x_42, x_44, x_10, x_11, x_40);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_mk_string_unchecked("squashing", 9, 9);
x_49 = lean_ctor_get(x_34, 2);
lean_inc(x_49);
x_50 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__9___boxed), 10, 5);
lean_closure_set(x_50, 0, x_49);
lean_closure_set(x_50, 1, x_3);
lean_closure_set(x_50, 2, x_17);
lean_closure_set(x_50, 3, x_39);
lean_closure_set(x_50, 4, x_46);
x_51 = lean_unbox(x_22);
x_52 = l_Lean_Elab_Tactic_NormCast_derive___lam__6(x_2, x_51, x_48, x_50, x_8, x_9, x_10, x_11, x_47);
return x_52;
}
else
{
uint8_t x_53; 
lean_dec(x_39);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_45);
if (x_53 == 0)
{
return x_45;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_45, 0);
x_55 = lean_ctor_get(x_45, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_45);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_dec(x_27);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_38;
}
}
else
{
lean_dec(x_27);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__0___boxed), 7, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__1___boxed), 9, 0);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__2___boxed), 9, 0);
x_11 = lean_mk_string_unchecked("Tactic", 6, 6);
x_12 = lean_mk_string_unchecked("norm_cast", 9, 9);
x_13 = l_Lean_Name_mkStr2(x_11, x_12);
lean_inc(x_9);
lean_inc(x_10);
lean_inc(x_13);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__10), 12, 7);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_13);
lean_closure_set(x_14, 2, x_2);
lean_closure_set(x_14, 3, x_10);
lean_closure_set(x_14, 4, x_9);
lean_closure_set(x_14, 5, x_10);
lean_closure_set(x_14, 6, x_9);
x_15 = lean_box(1);
x_16 = lean_mk_string_unchecked("", 0, 0);
x_17 = lean_unbox(x_15);
x_18 = l_Lean_withTraceNode___at___Lean_Meta_processPostponed_spec__0(lean_box(0), x_13, x_8, x_14, x_17, x_16, x_3, x_4, x_5, x_6, x_7);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_NormCast_derive___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_NormCast_derive___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_NormCast_derive___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_NormCast_derive___lam__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_NormCast_derive___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_NormCast_derive___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_Elab_Tactic_NormCast_derive___lam__6(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Elab_Tactic_NormCast_derive___lam__7(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_9);
lean_dec(x_9);
x_18 = l_Lean_Elab_Tactic_NormCast_derive___lam__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_10);
lean_dec(x_10);
x_17 = l_Lean_Elab_Tactic_NormCast_derive___lam__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_NormCast_derive___lam__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
lean_inc(x_3);
x_126 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_3, x_7, x_10);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = l_Lean_Expr_hasExprMVar(x_127);
lean_dec(x_127);
if (x_129 == 0)
{
x_65 = x_4;
x_66 = x_5;
x_67 = x_6;
x_68 = x_7;
x_69 = x_8;
x_70 = x_9;
x_71 = x_128;
goto block_125;
}
else
{
lean_object* x_130; 
x_130 = l_Lean_Elab_Term_tryPostpone(x_4, x_5, x_6, x_7, x_8, x_9, x_128);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
lean_dec(x_130);
x_65 = x_4;
x_66 = x_5;
x_67 = x_6;
x_68 = x_7;
x_69 = x_8;
x_70 = x_9;
x_71 = x_131;
goto block_125;
}
else
{
uint8_t x_132; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_132 = !lean_is_exclusive(x_130);
if (x_132 == 0)
{
return x_130;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_130, 0);
x_134 = lean_ctor_get(x_130, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_130);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
block_64:
{
lean_object* x_21; 
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_21 = l_Lean_Elab_Tactic_NormCast_derive(x_15, x_13, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_12);
lean_inc(x_24);
x_25 = l_Lean_Meta_isExprDefEq(x_24, x_12, x_16, x_17, x_18, x_19, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_3);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_mk_string_unchecked("mod_cast", 8, 8);
x_30 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = l_Lean_MessageData_ofFormat(x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_box(0);
x_34 = lean_box(0);
x_35 = l_Lean_Elab_Term_throwTypeMismatchError(lean_box(0), x_32, x_12, x_24, x_11, x_33, x_34, x_16, x_17, x_18, x_19, x_28);
lean_dec(x_32);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
return x_35;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_35);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_24);
lean_dec(x_12);
x_40 = lean_ctor_get(x_25, 1);
lean_inc(x_40);
lean_dec(x_25);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_41 = l_Lean_Meta_Simp_Result_mkEqSymm(x_3, x_14, x_16, x_17, x_18, x_19, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_44 = l_Lean_Meta_Simp_Result_mkEqTrans(x_22, x_42, x_16, x_17, x_18, x_19, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Meta_Simp_Result_mkCast(x_45, x_11, x_16, x_17, x_18, x_19, x_46);
return x_47;
}
else
{
uint8_t x_48; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_11);
x_48 = !lean_is_exclusive(x_44);
if (x_48 == 0)
{
return x_44;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_44, 0);
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_44);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_11);
x_52 = !lean_is_exclusive(x_41);
if (x_52 == 0)
{
return x_41;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_41, 0);
x_54 = lean_ctor_get(x_41, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_41);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_56 = !lean_is_exclusive(x_25);
if (x_56 == 0)
{
return x_25;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_25, 0);
x_58 = lean_ctor_get(x_25, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_25);
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
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_60 = !lean_is_exclusive(x_21);
if (x_60 == 0)
{
return x_21;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_21, 0);
x_62 = lean_ctor_get(x_21, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_21);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
block_125:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; lean_object* x_91; 
x_72 = lean_unsigned_to_nat(100000u);
x_73 = lean_unsigned_to_nat(2u);
x_74 = lean_box(0);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 20);
lean_ctor_set(x_76, 0, x_72);
lean_ctor_set(x_76, 1, x_73);
x_77 = lean_unbox(x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*2, x_77);
lean_ctor_set_uint8(x_76, sizeof(void*)*2 + 1, x_1);
x_78 = lean_unbox(x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*2 + 2, x_78);
x_79 = lean_unbox(x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*2 + 3, x_79);
x_80 = lean_unbox(x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*2 + 4, x_80);
x_81 = lean_unbox(x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*2 + 5, x_81);
x_82 = lean_unbox(x_75);
lean_ctor_set_uint8(x_76, sizeof(void*)*2 + 6, x_82);
x_83 = lean_unbox(x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*2 + 7, x_83);
x_84 = lean_unbox(x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*2 + 8, x_84);
x_85 = lean_unbox(x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*2 + 9, x_85);
x_86 = lean_unbox(x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*2 + 10, x_86);
x_87 = lean_unbox(x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*2 + 11, x_87);
lean_ctor_set_uint8(x_76, sizeof(void*)*2 + 12, x_1);
lean_ctor_set_uint8(x_76, sizeof(void*)*2 + 13, x_1);
x_88 = lean_unbox(x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*2 + 14, x_88);
x_89 = lean_unbox(x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*2 + 15, x_89);
x_90 = lean_unbox(x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*2 + 16, x_90);
lean_ctor_set_uint8(x_76, sizeof(void*)*2 + 17, x_1);
lean_ctor_set_uint8(x_76, sizeof(void*)*2 + 18, x_1);
lean_ctor_set_uint8(x_76, sizeof(void*)*2 + 19, x_1);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_76);
lean_inc(x_3);
x_91 = l_Lean_Elab_Tactic_NormCast_derive(x_3, x_76, x_67, x_68, x_69, x_70, x_71);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_ctor_get(x_92, 0);
lean_inc(x_94);
lean_inc(x_94);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
lean_inc(x_70);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
x_96 = l_Lean_Elab_Term_elabTerm(x_2, x_95, x_1, x_1, x_65, x_66, x_67, x_68, x_69, x_70, x_93);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_101; lean_object* x_102; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_box(0);
x_100 = lean_unbox(x_99);
x_101 = lean_unbox(x_74);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
x_102 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_100, x_101, x_65, x_66, x_67, x_68, x_69, x_70, x_98);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_97);
x_104 = lean_infer_type(x_97, x_67, x_68, x_69, x_70, x_103);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_105, x_68, x_106);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = l_Lean_Expr_hasExprMVar(x_108);
if (x_110 == 0)
{
lean_dec(x_66);
lean_dec(x_65);
x_11 = x_97;
x_12 = x_94;
x_13 = x_76;
x_14 = x_92;
x_15 = x_108;
x_16 = x_67;
x_17 = x_68;
x_18 = x_69;
x_19 = x_70;
x_20 = x_109;
goto block_64;
}
else
{
lean_object* x_111; 
x_111 = l_Lean_Elab_Term_tryPostpone(x_65, x_66, x_67, x_68, x_69, x_70, x_109);
lean_dec(x_66);
lean_dec(x_65);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
x_11 = x_97;
x_12 = x_94;
x_13 = x_76;
x_14 = x_92;
x_15 = x_108;
x_16 = x_67;
x_17 = x_68;
x_18 = x_69;
x_19 = x_70;
x_20 = x_112;
goto block_64;
}
else
{
uint8_t x_113; 
lean_dec(x_108);
lean_dec(x_97);
lean_dec(x_94);
lean_dec(x_92);
lean_dec(x_76);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_3);
x_113 = !lean_is_exclusive(x_111);
if (x_113 == 0)
{
return x_111;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_111, 0);
x_115 = lean_ctor_get(x_111, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_111);
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
lean_dec(x_97);
lean_dec(x_94);
lean_dec(x_92);
lean_dec(x_76);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_3);
return x_104;
}
}
else
{
uint8_t x_117; 
lean_dec(x_97);
lean_dec(x_94);
lean_dec(x_92);
lean_dec(x_76);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_3);
x_117 = !lean_is_exclusive(x_102);
if (x_117 == 0)
{
return x_102;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_102, 0);
x_119 = lean_ctor_get(x_102, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_102);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
lean_dec(x_94);
lean_dec(x_92);
lean_dec(x_76);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_3);
return x_96;
}
}
else
{
uint8_t x_121; 
lean_dec(x_76);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_3);
lean_dec(x_2);
x_121 = !lean_is_exclusive(x_91);
if (x_121 == 0)
{
return x_91;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_91, 0);
x_123 = lean_ctor_get(x_91, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_91);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_mk_string_unchecked("Lean", 4, 4);
x_11 = lean_mk_string_unchecked("modCast", 7, 7);
x_12 = l_Lean_Name_mkStr2(x_10, x_11);
lean_inc(x_1);
x_13 = l_Lean_Syntax_isOfKind(x_1, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
lean_dec(x_1);
x_17 = lean_box(x_13);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___boxed), 10, 2);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_16);
x_19 = l_Lean_Elab_Term_withExpectedType(x_2, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("modCast", 7, 7);
lean_inc(x_3);
x_5 = l_Lean_Name_mkStr2(x_3, x_4);
x_6 = lean_mk_string_unchecked("Elab", 4, 4);
x_7 = lean_mk_string_unchecked("Tactic", 6, 6);
x_8 = lean_mk_string_unchecked("NormCast", 8, 8);
x_9 = lean_mk_string_unchecked("elabModCast", 11, 11);
x_10 = l_Lean_Name_mkStr5(x_3, x_6, x_7, x_8, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_elabModCast), 9, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_5, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("NormCast", 8, 8);
x_6 = lean_mk_string_unchecked("elabModCast", 11, 11);
x_7 = l_Lean_Name_mkStr5(x_2, x_3, x_4, x_5, x_6);
x_8 = lean_unsigned_to_nat(209u);
x_9 = lean_unsigned_to_nat(29u);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_unsigned_to_nat(224u);
x_12 = lean_unsigned_to_nat(31u);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set(x_14, 3, x_12);
x_15 = lean_unsigned_to_nat(33u);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_unsigned_to_nat(44u);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_18);
lean_ctor_set(x_19, 3, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_addBuiltinDeclarationRanges(x_7, x_20, x_1);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastTarget___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_12);
x_14 = l_Lean_MVarId_getType(x_12, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_15, x_7, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_19);
x_21 = l_Lean_Elab_Tactic_NormCast_derive(x_19, x_1, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_24 = l_Lean_Meta_applySimpResultToTarget(x_12, x_19, x_22, x_6, x_7, x_8, x_9, x_23);
lean_dec(x_19);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_box(0);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_27);
lean_ctor_set(x_17, 0, x_25);
x_28 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_17, x_3, x_6, x_7, x_8, x_9, x_26);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_28;
}
else
{
uint8_t x_29; 
lean_free_object(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 0);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_24);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_33 = !lean_is_exclusive(x_21);
if (x_33 == 0)
{
return x_21;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_21, 0);
x_35 = lean_ctor_get(x_21, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_21);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_17, 0);
x_38 = lean_ctor_get(x_17, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_37);
x_39 = l_Lean_Elab_Tactic_NormCast_derive(x_37, x_1, x_6, x_7, x_8, x_9, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_42 = l_Lean_Meta_applySimpResultToTarget(x_12, x_37, x_40, x_6, x_7, x_8, x_9, x_41);
lean_dec(x_37);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_46, x_3, x_6, x_7, x_8, x_9, x_44);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_48 = lean_ctor_get(x_42, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_42, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_50 = x_42;
} else {
 lean_dec_ref(x_42);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_37);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_52 = lean_ctor_get(x_39, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_39, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_54 = x_39;
} else {
 lean_dec_ref(x_39);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_14);
if (x_56 == 0)
{
return x_14;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_14, 0);
x_58 = lean_ctor_get(x_14, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_14);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_11);
if (x_60 == 0)
{
return x_11;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_11, 0);
x_62 = lean_ctor_get(x_11, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_11);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastTarget(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_normCastTarget___lam__0___boxed), 10, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Elab_Tactic_withMainContext___redArg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastTarget___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_NormCast_normCastTarget___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastTarget___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_NormCast_normCastTarget(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastHyp___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_7);
lean_inc(x_1);
x_15 = l_Lean_FVarId_getDecl___redArg(x_1, x_7, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_73; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_73 = lean_ctor_get(x_16, 3);
lean_inc(x_73);
lean_dec(x_16);
x_18 = x_73;
goto block_72;
block_72:
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_18, x_8, x_17);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_23 = l_Lean_Elab_Tactic_NormCast_derive(x_21, x_2, x_7, x_8, x_9, x_10, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_box(0);
x_27 = lean_unbox(x_26);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_28 = l_Lean_Meta_applySimpResultToLocalDecl(x_13, x_1, x_24, x_27, x_7, x_8, x_9, x_10, x_25);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_free_object(x_19);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_box(0);
x_32 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_31, x_4, x_7, x_8, x_9, x_10, x_30);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_dec(x_28);
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
lean_dec(x_29);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_box(0);
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 1, x_36);
lean_ctor_set(x_19, 0, x_35);
x_37 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_19, x_4, x_7, x_8, x_9, x_10, x_33);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_free_object(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_38 = !lean_is_exclusive(x_28);
if (x_38 == 0)
{
return x_28;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_28, 0);
x_40 = lean_ctor_get(x_28, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_28);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_free_object(x_19);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_23);
if (x_42 == 0)
{
return x_23;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_23, 0);
x_44 = lean_ctor_get(x_23, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_23);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_19, 0);
x_47 = lean_ctor_get(x_19, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_48 = l_Lean_Elab_Tactic_NormCast_derive(x_46, x_2, x_7, x_8, x_9, x_10, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_box(0);
x_52 = lean_unbox(x_51);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_53 = l_Lean_Meta_applySimpResultToLocalDecl(x_13, x_1, x_49, x_52, x_7, x_8, x_9, x_10, x_50);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_box(0);
x_57 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_56, x_4, x_7, x_8, x_9, x_10, x_55);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
lean_dec(x_53);
x_59 = lean_ctor_get(x_54, 0);
lean_inc(x_59);
lean_dec(x_54);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_62, x_4, x_7, x_8, x_9, x_10, x_58);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_64 = lean_ctor_get(x_53, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_53, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_66 = x_53;
} else {
 lean_dec_ref(x_53);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_68 = lean_ctor_get(x_48, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_48, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_70 = x_48;
} else {
 lean_dec_ref(x_48);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_15);
if (x_74 == 0)
{
return x_15;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_15, 0);
x_76 = lean_ctor_get(x_15, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_15);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_12);
if (x_78 == 0)
{
return x_12;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_12, 0);
x_80 = lean_ctor_get(x_12, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_12);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastHyp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_normCastHyp___lam__0___boxed), 11, 2);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_1);
x_13 = l_Lean_Elab_Tactic_withMainContext___redArg(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastHyp___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_NormCast_normCastHyp___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastHyp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_NormCast_normCastHyp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_eq(x_3, x_4);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
x_16 = lean_array_uget(x_2, x_3);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_17 = l_Lean_Elab_Tactic_NormCast_normCastHyp(x_1, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_usize_of_nat(x_20);
x_22 = lean_usize_add(x_3, x_21);
x_3 = x_22;
x_5 = x_18;
x_14 = x_19;
goto _start;
}
else
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_17;
}
}
else
{
lean_object* x_24; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_5);
lean_ctor_set(x_24, 1, x_14);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_13 = l_Lean_Elab_Tactic_NormCast_normCastTarget(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Elab_Tactic_getMainGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_18 = l_Lean_MVarId_getNondepPropHyps(x_16, x_8, x_9, x_10, x_11, x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_array_get_size(x_20);
x_23 = lean_box(0);
x_24 = lean_nat_dec_lt(x_3, x_22);
if (x_24 == 0)
{
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_ctor_set(x_18, 0, x_23);
return x_18;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_22, x_22);
if (x_25 == 0)
{
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_ctor_set(x_18, 0, x_23);
return x_18;
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; 
lean_free_object(x_18);
x_26 = lean_usize_of_nat(x_3);
x_27 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_28 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0(x_2, x_20, x_26, x_27, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_21);
lean_dec(x_20);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_31 = lean_array_get_size(x_29);
x_32 = lean_box(0);
x_33 = lean_nat_dec_lt(x_3, x_31);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_30);
return x_34;
}
else
{
uint8_t x_35; 
x_35 = lean_nat_dec_le(x_31, x_31);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_30);
return x_36;
}
else
{
size_t x_37; size_t x_38; lean_object* x_39; 
x_37 = lean_usize_of_nat(x_3);
x_38 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_39 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0(x_2, x_29, x_37, x_38, x_32, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_30);
lean_dec(x_29);
return x_39;
}
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_18);
if (x_40 == 0)
{
return x_18;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_18, 0);
x_42 = lean_ctor_get(x_18, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_18);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_44 = !lean_is_exclusive(x_15);
if (x_44 == 0)
{
return x_15;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_15, 0);
x_46 = lean_ctor_get(x_15, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_15);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
else
{
lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
lean_dec(x_1);
if (x_49 == 0)
{
x_50 = x_4;
x_51 = x_5;
x_52 = x_6;
x_53 = x_7;
x_54 = x_8;
x_55 = x_9;
x_56 = x_10;
x_57 = x_11;
x_58 = x_12;
goto block_85;
}
else
{
lean_object* x_86; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_86 = l_Lean_Elab_Tactic_NormCast_normCastTarget(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_50 = x_4;
x_51 = x_5;
x_52 = x_6;
x_53 = x_7;
x_54 = x_8;
x_55 = x_9;
x_56 = x_10;
x_57 = x_11;
x_58 = x_87;
goto block_85;
}
else
{
lean_dec(x_48);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_86;
}
}
block_85:
{
lean_object* x_59; 
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_59 = l_Lean_Elab_Tactic_getFVarIds(x_48, x_50, x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_ctor_get(x_59, 1);
x_63 = lean_array_get_size(x_61);
x_64 = lean_box(0);
x_65 = lean_nat_dec_lt(x_3, x_63);
if (x_65 == 0)
{
lean_dec(x_63);
lean_dec(x_61);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_2);
lean_ctor_set(x_59, 0, x_64);
return x_59;
}
else
{
uint8_t x_66; 
x_66 = lean_nat_dec_le(x_63, x_63);
if (x_66 == 0)
{
lean_dec(x_63);
lean_dec(x_61);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_2);
lean_ctor_set(x_59, 0, x_64);
return x_59;
}
else
{
size_t x_67; size_t x_68; lean_object* x_69; 
lean_free_object(x_59);
x_67 = lean_usize_of_nat(x_3);
x_68 = lean_usize_of_nat(x_63);
lean_dec(x_63);
x_69 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0(x_2, x_61, x_67, x_68, x_64, x_50, x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_62);
lean_dec(x_61);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_70 = lean_ctor_get(x_59, 0);
x_71 = lean_ctor_get(x_59, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_59);
x_72 = lean_array_get_size(x_70);
x_73 = lean_box(0);
x_74 = lean_nat_dec_lt(x_3, x_72);
if (x_74 == 0)
{
lean_object* x_75; 
lean_dec(x_72);
lean_dec(x_70);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_2);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_71);
return x_75;
}
else
{
uint8_t x_76; 
x_76 = lean_nat_dec_le(x_72, x_72);
if (x_76 == 0)
{
lean_object* x_77; 
lean_dec(x_72);
lean_dec(x_70);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_2);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_73);
lean_ctor_set(x_77, 1, x_71);
return x_77;
}
else
{
size_t x_78; size_t x_79; lean_object* x_80; 
x_78 = lean_usize_of_nat(x_3);
x_79 = lean_usize_of_nat(x_72);
lean_dec(x_72);
x_80 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0(x_2, x_70, x_78, x_79, x_73, x_50, x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_71);
lean_dec(x_70);
return x_80;
}
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_2);
x_81 = !lean_is_exclusive(x_59);
if (x_81 == 0)
{
return x_59;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_59, 0);
x_83 = lean_ctor_get(x_59, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_59);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_mk_string_unchecked("Lean", 4, 4);
x_12 = lean_mk_string_unchecked("Parser", 6, 6);
x_13 = lean_mk_string_unchecked("Tactic", 6, 6);
x_14 = lean_mk_string_unchecked("normCast0", 9, 9);
x_15 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_14);
lean_inc(x_1);
x_16 = l_Lean_Syntax_isOfKind(x_1, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_10);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_unsigned_to_nat(1u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
x_41 = lean_unsigned_to_nat(2u);
x_42 = l_Lean_Syntax_getArg(x_1, x_41);
lean_dec(x_1);
x_43 = l_Lean_Syntax_isNone(x_42);
if (x_43 == 0)
{
uint8_t x_44; 
lean_inc(x_42);
x_44 = l_Lean_Syntax_matchesNull(x_42, x_19);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_42);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_45 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_10);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = l_Lean_Syntax_getArg(x_42, x_18);
lean_dec(x_42);
x_47 = l_Lean_Elab_Tactic_expandLocation(x_46);
lean_dec(x_46);
x_21 = x_7;
x_22 = x_3;
x_23 = x_5;
x_24 = x_4;
x_25 = x_10;
x_26 = x_6;
x_27 = x_9;
x_28 = x_8;
x_29 = x_2;
x_30 = x_47;
goto block_40;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_42);
x_48 = lean_mk_empty_array_with_capacity(x_18);
x_49 = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_16);
x_21 = x_7;
x_22 = x_3;
x_23 = x_5;
x_24 = x_4;
x_25 = x_10;
x_26 = x_6;
x_27 = x_9;
x_28 = x_8;
x_29 = x_2;
x_30 = x_49;
goto block_40;
}
block_40:
{
lean_object* x_31; 
lean_inc(x_27);
lean_inc(x_21);
lean_inc(x_26);
lean_inc(x_23);
lean_inc(x_24);
x_31 = l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg(x_20, x_29, x_24, x_23, x_26, x_21, x_28, x_27, x_25);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_evalNormCast0___lam__0___boxed), 12, 3);
lean_closure_set(x_34, 0, x_30);
lean_closure_set(x_34, 1, x_32);
lean_closure_set(x_34, 2, x_18);
x_35 = l_Lean_Elab_Tactic_withMainContext___redArg(x_34, x_29, x_22, x_24, x_23, x_26, x_21, x_28, x_27, x_33);
lean_dec(x_26);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0(x_1, x_2, x_15, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_10);
lean_dec(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_NormCast_evalNormCast0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("normCast0", 9, 9);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("NormCast", 8, 8);
x_10 = lean_mk_string_unchecked("evalNormCast0", 13, 13);
x_11 = l_Lean_Name_mkStr5(x_3, x_8, x_5, x_9, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_evalNormCast0), 10, 0);
x_13 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_11, x_12, x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("NormCast", 8, 8);
x_6 = lean_mk_string_unchecked("evalNormCast0", 13, 13);
x_7 = l_Lean_Name_mkStr5(x_2, x_3, x_4, x_5, x_6);
x_8 = lean_unsigned_to_nat(241u);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_unsigned_to_nat(253u);
x_12 = lean_unsigned_to_nat(31u);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set(x_14, 3, x_12);
x_15 = lean_unsigned_to_nat(4u);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_unsigned_to_nat(17u);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_18);
lean_ctor_set(x_19, 3, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_addBuiltinDeclarationRanges(x_7, x_20, x_1);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_10 = l_Lean_Elab_Tactic_Conv_getLhs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(100000u);
x_14 = lean_unsigned_to_nat(2u);
x_15 = lean_box(0);
x_16 = lean_box(1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 20);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_14);
x_19 = lean_unbox(x_15);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_19);
x_20 = lean_unbox(x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 1, x_20);
x_21 = lean_unbox(x_15);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 2, x_21);
x_22 = lean_unbox(x_15);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 3, x_22);
x_23 = lean_unbox(x_15);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 4, x_23);
x_24 = lean_unbox(x_15);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 5, x_24);
x_25 = lean_unbox(x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 6, x_25);
x_26 = lean_unbox(x_15);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 7, x_26);
x_27 = lean_unbox(x_15);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 8, x_27);
x_28 = lean_unbox(x_15);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 9, x_28);
x_29 = lean_unbox(x_15);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 10, x_29);
x_30 = lean_unbox(x_15);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 11, x_30);
x_31 = lean_unbox(x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 12, x_31);
x_32 = lean_unbox(x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 13, x_32);
x_33 = lean_unbox(x_15);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 14, x_33);
x_34 = lean_unbox(x_15);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 15, x_34);
x_35 = lean_unbox(x_15);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 16, x_35);
x_36 = lean_unbox(x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 17, x_36);
x_37 = lean_unbox(x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 18, x_37);
x_38 = lean_unbox(x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 19, x_38);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_39 = l_Lean_Elab_Tactic_NormCast_derive(x_11, x_18, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Elab_Tactic_Conv_applySimpResult(x_40, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_41);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_39);
if (x_43 == 0)
{
return x_39;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_39, 0);
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_39);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_10);
if (x_47 == 0)
{
return x_10;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_10, 0);
x_49 = lean_ctor_get(x_10, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_10);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg___lam__0), 9, 0);
x_11 = l_Lean_Elab_Tactic_withMainContext___redArg(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_NormCast_evalConvNormCast(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("Conv", 4, 4);
x_7 = lean_mk_string_unchecked("normCast", 8, 8);
lean_inc(x_5);
lean_inc(x_3);
x_8 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_7);
x_9 = lean_mk_string_unchecked("Elab", 4, 4);
x_10 = lean_mk_string_unchecked("NormCast", 8, 8);
x_11 = lean_mk_string_unchecked("evalConvNormCast", 16, 16);
x_12 = l_Lean_Name_mkStr5(x_3, x_9, x_5, x_10, x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_evalConvNormCast___boxed), 10, 0);
x_14 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_8, x_12, x_13, x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("NormCast", 8, 8);
x_6 = lean_mk_string_unchecked("evalConvNormCast", 16, 16);
x_7 = l_Lean_Name_mkStr5(x_2, x_3, x_4, x_5, x_6);
x_8 = lean_unsigned_to_nat(256u);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_unsigned_to_nat(258u);
x_12 = lean_unsigned_to_nat(41u);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set(x_14, 3, x_12);
x_15 = lean_unsigned_to_nat(4u);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_unsigned_to_nat(20u);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_18);
lean_ctor_set(x_19, 3, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_addBuiltinDeclarationRanges(x_7, x_20, x_1);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_unsigned_to_nat(5u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = l_Lean_Elab_Tactic_expandOptLocation(x_15);
lean_dec(x_15);
x_17 = l_Lean_Elab_Tactic_simpLocation(x_2, x_3, x_4, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_box(0);
x_12 = lean_box(0);
x_13 = l_Lean_Meta_NormCast_pushCastExt;
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_SimpExtension_getTheorems___boxed), 4, 1);
lean_closure_set(x_14, 0, x_13);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_11);
lean_closure_set(x_15, 2, x_12);
lean_closure_set(x_15, 3, x_11);
lean_closure_set(x_15, 4, x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_16 = l_Lean_Elab_Tactic_withMainContext___redArg(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 2);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_unbox(x_11);
x_23 = l_Lean_Meta_Simp_Context_setFailIfUnchanged(x_19, x_22);
lean_dec(x_19);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_evalPushCast___lam__0___boxed), 13, 3);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_23);
lean_closure_set(x_24, 2, x_20);
x_25 = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(x_21, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
lean_dec(x_21);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
return x_16;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_16);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_NormCast_evalPushCast___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("pushCast", 8, 8);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("NormCast", 8, 8);
x_10 = lean_mk_string_unchecked("evalPushCast", 12, 12);
x_11 = l_Lean_Name_mkStr5(x_3, x_8, x_5, x_9, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_evalPushCast), 10, 0);
x_13 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_11, x_12, x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("NormCast", 8, 8);
x_6 = lean_mk_string_unchecked("evalPushCast", 12, 12);
x_7 = l_Lean_Name_mkStr5(x_2, x_3, x_4, x_5, x_6);
x_8 = lean_unsigned_to_nat(261u);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_unsigned_to_nat(266u);
x_12 = lean_unsigned_to_nat(78u);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set(x_14, 3, x_12);
x_15 = lean_unsigned_to_nat(4u);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_unsigned_to_nat(16u);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_18);
lean_ctor_set(x_19, 3, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_addBuiltinDeclarationRanges(x_7, x_20, x_1);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_st_mk_ref(x_1, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
x_10 = l_Lean_realizeGlobalConstNoOverload(x_2, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = lean_unsigned_to_nat(1000u);
x_15 = lean_unbox(x_13);
lean_inc(x_8);
x_16 = l_Lean_Meta_NormCast_addElim(x_11, x_15, x_14, x_3, x_8, x_4, x_5, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_8, x_18);
lean_dec(x_8);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_17);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_dec(x_8);
return x_16;
}
}
else
{
uint8_t x_24; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_24 = !lean_is_exclusive(x_10);
if (x_24 == 0)
{
return x_10;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_10, 0);
x_26 = lean_ctor_get(x_10, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_10);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("Parser", 6, 6);
x_7 = lean_mk_string_unchecked("Tactic", 6, 6);
x_8 = lean_mk_string_unchecked("normCastAddElim", 15, 15);
x_9 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_8);
lean_inc(x_1);
x_10 = l_Lean_Syntax_isOfKind(x_1, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
x_14 = lean_mk_string_unchecked("ident", 5, 5);
x_15 = l_Lean_Name_mkStr1(x_14);
lean_inc(x_13);
x_16 = l_Lean_Syntax_isOfKind(x_13, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_13);
x_17 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint64_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; lean_object* x_40; lean_object* x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_box(0);
x_20 = lean_box(1);
x_21 = lean_box(0);
x_22 = lean_box(2);
x_23 = lean_alloc_ctor(0, 0, 18);
x_24 = lean_unbox(x_19);
lean_ctor_set_uint8(x_23, 0, x_24);
x_25 = lean_unbox(x_19);
lean_ctor_set_uint8(x_23, 1, x_25);
x_26 = lean_unbox(x_19);
lean_ctor_set_uint8(x_23, 2, x_26);
x_27 = lean_unbox(x_19);
lean_ctor_set_uint8(x_23, 3, x_27);
x_28 = lean_unbox(x_19);
lean_ctor_set_uint8(x_23, 4, x_28);
lean_ctor_set_uint8(x_23, 5, x_16);
lean_ctor_set_uint8(x_23, 6, x_16);
x_29 = lean_unbox(x_19);
lean_ctor_set_uint8(x_23, 7, x_29);
lean_ctor_set_uint8(x_23, 8, x_16);
x_30 = lean_unbox(x_20);
lean_ctor_set_uint8(x_23, 9, x_30);
x_31 = lean_unbox(x_21);
lean_ctor_set_uint8(x_23, 10, x_31);
lean_ctor_set_uint8(x_23, 11, x_16);
lean_ctor_set_uint8(x_23, 12, x_16);
lean_ctor_set_uint8(x_23, 13, x_16);
x_32 = lean_unbox(x_22);
lean_ctor_set_uint8(x_23, 14, x_32);
lean_ctor_set_uint8(x_23, 15, x_16);
lean_ctor_set_uint8(x_23, 16, x_16);
lean_ctor_set_uint8(x_23, 17, x_16);
x_33 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_23);
x_34 = lean_box(0);
x_35 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_35);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_unsigned_to_nat(2u);
x_38 = lean_unsigned_to_nat(5u);
x_39 = lean_usize_of_nat(x_38);
x_40 = lean_usize_to_nat(x_39);
x_41 = lean_nat_pow(x_37, x_40);
lean_dec(x_40);
x_42 = lean_usize_of_nat(x_41);
lean_dec(x_41);
x_43 = lean_usize_to_nat(x_42);
x_44 = lean_mk_empty_array_with_capacity(x_43);
lean_dec(x_43);
lean_inc(x_44);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
lean_inc(x_44);
x_46 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_46, 2, x_18);
lean_ctor_set(x_46, 3, x_18);
lean_ctor_set_usize(x_46, 4, x_39);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_47, 2, x_34);
x_48 = lean_mk_empty_array_with_capacity(x_18);
x_49 = lean_box(0);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_51, 0, x_23);
lean_ctor_set(x_51, 1, x_34);
lean_ctor_set(x_51, 2, x_47);
lean_ctor_set(x_51, 3, x_48);
lean_ctor_set(x_51, 4, x_49);
lean_ctor_set(x_51, 5, x_18);
lean_ctor_set(x_51, 6, x_50);
lean_ctor_set_uint64(x_51, sizeof(void*)*7, x_33);
x_52 = lean_unbox(x_19);
lean_ctor_set_uint8(x_51, sizeof(void*)*7 + 8, x_52);
x_53 = lean_unbox(x_19);
lean_ctor_set_uint8(x_51, sizeof(void*)*7 + 9, x_53);
x_54 = lean_unbox(x_19);
lean_ctor_set_uint8(x_51, sizeof(void*)*7 + 10, x_54);
lean_inc(x_35);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_35);
lean_inc(x_35);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_35);
lean_inc(x_35);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_35);
lean_inc(x_35);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_35);
lean_inc(x_35);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_35);
lean_inc(x_35);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_35);
lean_inc(x_55);
x_61 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_61, 0, x_18);
lean_ctor_set(x_61, 1, x_18);
lean_ctor_set(x_61, 2, x_18);
lean_ctor_set(x_61, 3, x_55);
lean_ctor_set(x_61, 4, x_56);
lean_ctor_set(x_61, 5, x_57);
lean_ctor_set(x_61, 6, x_58);
lean_ctor_set(x_61, 7, x_59);
lean_ctor_set(x_61, 8, x_60);
lean_inc(x_35);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_35);
lean_inc(x_35);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_35);
lean_inc(x_35);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_35);
lean_inc(x_35);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_35);
lean_inc(x_65);
lean_inc(x_62);
x_66 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_66, 0, x_62);
lean_ctor_set(x_66, 1, x_63);
lean_ctor_set(x_66, 2, x_64);
lean_ctor_set(x_66, 3, x_62);
lean_ctor_set(x_66, 4, x_65);
lean_ctor_set(x_66, 5, x_65);
lean_inc(x_44);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_44);
x_68 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_44);
lean_ctor_set(x_68, 2, x_18);
lean_ctor_set(x_68, 3, x_18);
lean_ctor_set_usize(x_68, 4, x_39);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_35);
lean_inc_n(x_55, 2);
x_70 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_70, 0, x_55);
lean_ctor_set(x_70, 1, x_55);
lean_ctor_set(x_70, 2, x_55);
lean_ctor_set(x_70, 3, x_69);
x_71 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_71, 0, x_61);
lean_ctor_set(x_71, 1, x_66);
lean_ctor_set(x_71, 2, x_34);
lean_ctor_set(x_71, 3, x_68);
lean_ctor_set(x_71, 4, x_70);
x_72 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_elabAddElim___lam__0___boxed), 6, 3);
lean_closure_set(x_72, 0, x_71);
lean_closure_set(x_72, 1, x_13);
lean_closure_set(x_72, 2, x_51);
x_73 = l_Lean_Elab_Command_liftCoreM___redArg(x_72, x_2, x_3, x_4);
return x_73;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_NormCast_elabAddElim___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_NormCast_elabAddElim(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("normCastAddElim", 15, 15);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("NormCast", 8, 8);
x_10 = lean_mk_string_unchecked("elabAddElim", 11, 11);
x_11 = l_Lean_Name_mkStr5(x_3, x_8, x_5, x_9, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_elabAddElim___boxed), 4, 0);
x_13 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_11, x_12, x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("NormCast", 8, 8);
x_6 = lean_mk_string_unchecked("elabAddElim", 11, 11);
x_7 = l_Lean_Name_mkStr5(x_2, x_3, x_4, x_5, x_6);
x_8 = lean_unsigned_to_nat(269u);
x_9 = lean_unsigned_to_nat(54u);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_unsigned_to_nat(274u);
x_12 = lean_unsigned_to_nat(31u);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set(x_14, 3, x_12);
x_15 = lean_unsigned_to_nat(58u);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_unsigned_to_nat(69u);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_18);
lean_ctor_set(x_19, 3, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_addBuiltinDeclarationRanges(x_7, x_20, x_1);
return x_21;
}
}
lean_object* initialize_Lean_Meta_Tactic_NormCast(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Conv_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_ElabRules(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_NormCast(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_NormCast(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_ElabRules(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_Elab_Tactic_NormCast_initFn____x40_Lean_Elab_Tactic_NormCast___hyg_5_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
