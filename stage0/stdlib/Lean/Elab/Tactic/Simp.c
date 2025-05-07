// Lean compiler output
// Module: Lean.Elab.Tactic.Simp
// Imports: Lean.Meta.Tactic.Simp Lean.Meta.Tactic.Replace Lean.Elab.BuiltinNotation Lean.Elab.Tactic.Basic Lean.Elab.Tactic.ElabTerm Lean.Elab.Tactic.Location Lean.Elab.Tactic.Config
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
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_Elab_Tactic_elabSimpArgs_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_1146_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_traceSimpCall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_go(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at___Lean_Elab_Tactic_elabSimpArgs_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logException___at___Lean_Elab_Tactic_closeUsingOrAdmit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpTheorems___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveId_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withTrackingZetaDeltaSet___at___Lean_Elab_Tactic_elabSimpArgs_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_dsimpGoal(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_Simp___hyg_6_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_private_to_user_name(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimp___lam__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_SimpTheoremsArray_isErased(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_elabConfig(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCtxCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addSimpTheorem___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs_isSimproc_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tactic_simp_trace;
lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_withMainContext_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_mkDischargeWrapper___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_mkSimpContext_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_mkSimpOnly_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at___Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___Lean_Elab_Tactic_traceSimpCall_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addSimpTheorem(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_expandOptLocation(lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Elab_Term_isLocalIdent_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_Elab_Tactic_elabSimpArgs_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpGoal(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpLocation_go(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_mkSimpOnly_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_mkDischargeWrapper___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpLocation___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_mkSimpOnly_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Match_isMatchEqnTheorem(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_getConstVal___at___Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_Elab_Tactic_elabSimpArgs_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_setSimpParams(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabCDotFunctionAlias_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_hasValue(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticToDischarge___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticToDischarge___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticToDischarge___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticToDischarge___redArg___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticToDischarge___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_getDSimpArgs_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_1146____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs_isSimproc_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfig(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SimpKind_noConfusion___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_SimpTheorems_isLemma(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___at___Lean_Meta_Match_initFn____x40_Lean_Meta_Match_MatchEqsExt___hyg_181__spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpLocation_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SimpKind_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SimpKind_noConfusion___redArg___lam__0(lean_object*);
lean_object* l_Lean_Meta_Simp_UsedSimps_toArray(lean_object*);
lean_object* l_Lean_Meta_getZetaDeltaFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName_loop___at___Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___at___Lean_Environment_realizeConst_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at___Lean_Elab_Tactic_elabSimpArgs_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_spec__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___Lean_Meta_SimpTheorems_erase___at___Lean_Elab_Tactic_elabSimpArgs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_unresolveNameGlobal_unresolveNameCore___at___Lean_unresolveNameGlobal___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__3_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimp__1(lean_object*);
lean_object* l_Lean_Meta_SimpTheorems_add(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getNondepPropHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAll___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addSimpTheorem___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName_loop___at___Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_spec__5_spec__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName_loop___at___Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticToDischarge(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___at___Lean_Meta_mkSimpExt_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getSimpParams___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_beqSimpKind____x40_Lean_Elab_Tactic_Simp___hyg_1730____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName_loop___at___Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticToDischarge___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_unresolveNameGlobal___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__3_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpLocation___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getSimpParams(lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_7019_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_spec__5_spec__5___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_isSimpOnly___boxed(lean_object*);
lean_object* l_Lean_getRevAliases(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_mkSimpOnly_spec__10(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___at___Lean_unresolveNameGlobal___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_instInhabitedSimpKind;
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Lean_log___at___Lean_logError___at___Lean_Elab_logException___at___Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__2_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___at___Lean_unresolveNameGlobal___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticToDischarge___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_mkSimpOnly_spec__8_spec__8___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_mkSimpContext_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SimpKind_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_Elab_Tactic_elabSimpArgs_spec__4___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SimpKind_toCtorIdx(uint8_t);
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_mkSimpOnly_spec__8_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_getSimpArgs_x3f(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Elab_Tactic_mkSimpContext_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withSimpDiagnostics(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_unresolveNameGlobal_unresolveNameCore___at___Lean_unresolveNameGlobal___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__3_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___Lean_resolveLocalName_loop___at___Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs_isSimproc_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_getSimprocs(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpTheorems_addDeclToUnfoldCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_abstractMVars(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___Lean_resolveLocalName_loop___at___Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkSep(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_mkSimpContext_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs___lam__0___boxed(lean_object**);
lean_object* l_Lean_Elab_Tactic_withMainContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addSimpTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigItemViews(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAll__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpOnly___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SimpKind_noConfusion___redArg(uint8_t, uint8_t);
lean_object* l_Lean_Meta_getPropHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___Lean_resolveLocalName_loop___at___Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDSimpConfigCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
lean_object* l_Lean_Name_componentsRev(lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_rootNamespace;
extern lean_object* l_Lean_warningAsError;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_Elab_Tactic_elabSimpArgs_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Elab_Tactic_mkSimpContext_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_mkSimpOnly_spec__8_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__3(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_mkSimpOnly_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isLet(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_isSimpOnly(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___Lean_Elab_Tactic_traceSimpCall_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpLocation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimp___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MacroScopesView_review(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_Elab_Tactic_elabSimpArgs_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_576_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_setSimpParams___boxed(lean_object*, lean_object*);
lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_eta(lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___Lean_LocalDecl_setBinderInfo_spec__0(lean_object*);
lean_object* l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_Elab_Tactic_elabSimpArgs_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_isSimproc___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpOnlyPos;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_unresolveNameGlobal_unresolveNameCore___at___Lean_unresolveNameGlobal___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__3_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_Elab_Term_runTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDSimpConfigCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_576____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_SimprocExtension_getSimprocs___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Name_appendCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpParamsPos;
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Elab_Tactic_mkSimpContext_spec__1___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfig___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_traceSimpCall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___Lean_resolveLocalName___at___Lean_Elab_Term_isLocalIdent_x3f_spec__0_spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_SimprocsArray_erase(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_isBuiltinSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpTheorems_addLetDeclToUnfold(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_Elab_Tactic_elabSimpArgs_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Context_setSimpTheorems(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAll___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___Lean_resolveLocalName___at___Lean_Elab_Term_isLocalIdent_x3f_spec__0_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instInhabitedSimpTheorems;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpContext(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withTrackingZetaDeltaSet___at___Lean_Elab_Tactic_elabSimpArgs_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Context_setZetaDeltaSet(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_mkSimpOnly_spec__8_spec__8___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_reportDiag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_mkSimpOnly_spec__10___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpExtension_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_go___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_SimpTheorems_isDeclToUnfold(lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_mkSimpContext_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterTR_loop___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withTrackingZetaDeltaSet___at___Lean_Elab_Tactic_elabSimpArgs_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Elab_Tactic_mkSimpContext_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_SimprocsArray_add(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withTrackingZetaDeltaSet___at___Lean_Elab_Tactic_elabSimpArgs_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutErrToSorry___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_Meta_SimpTheorems_addConst(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_is_inaccessible_user_name(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_Simp___hyg_576_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at___Lean_Elab_Tactic_elabSimpArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Origin_converse(lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instBEqSimpKind;
lean_object* l_Array_foldlMUnsafe_fold___at___Lean_unresolveNameGlobal___at___Lean_PrettyPrinter_Delaborator_delabConst_spec__1_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkUnknownIdentifierMessage(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpContext___lam__0(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCtxCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpContext___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SimpKind_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDSimpConfigCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at___Lean_Elab_Tactic_elabSimpArgs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_Elab_Tactic_elabSimpArgs_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimp___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_unresolveNameGlobal_unresolveNameCore___at___Lean_unresolveNameGlobal___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__3_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCtxCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpTheorems_addDeclToUnfold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_mkDischargeWrapper___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpExtension_getTheorems___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___Lean_Meta_SimpTheorems_erase___at___Lean_Elab_Tactic_elabSimpArgs_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_Elab_Tactic_elabSimpArgs_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimp__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs_isSimproc_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_beqSimpKind____x40_Lean_Elab_Tactic_Simp___hyg_1730_(uint8_t, uint8_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SimpKind_noConfusion___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDSimpConfigCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_mkDischargeWrapper(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_unresolveNameGlobal___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_Simp___hyg_1146_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_getSimprocExtension_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalExpr_x27(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpLocation___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Expr_isFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpLocation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpTheorems_eraseCore(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_SimpTheoremsArray_addTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_spec__5_spec__5___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_Elab_Tactic_elabSimpArgs_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___Lean_resolveLocalName_loop___at___Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_spec__5_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCtxCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticToDischarge___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_Elab_Tactic_elabSimpArgs_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpLocation___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpOnlyBuiltins;
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_Simp___hyg_6_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Meta", 4, 4);
x_9 = lean_mk_string_unchecked("Simp", 4, 4);
x_10 = lean_mk_string_unchecked("Config", 6, 6);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
x_14 = l_Lean_Meta_evalExpr_x27(lean_box(0), x_11, x_1, x_13, x_2, x_3, x_4, x_5, x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_Simp___hyg_6_(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6_(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_66 = lean_mk_string_unchecked("Config", 6, 6);
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
x_87 = l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_Simp___hyg_6_(x_83, x_5, x_6, x_61, x_8, x_84);
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
x_11 = x_89;
x_12 = x_6;
x_13 = x_83;
x_14 = x_5;
x_15 = x_4;
x_16 = x_88;
x_17 = x_87;
x_18 = x_3;
x_19 = x_61;
x_20 = x_91;
goto block_35;
}
else
{
x_10 = x_8;
x_11 = x_89;
x_12 = x_6;
x_13 = x_83;
x_14 = x_5;
x_15 = x_4;
x_16 = x_88;
x_17 = x_87;
x_18 = x_3;
x_19 = x_61;
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
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 3, x_85);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 4, x_85);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 5, x_85);
x_103 = lean_unbox(x_101);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 6, x_103);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 7, x_85);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 8, x_85);
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
x_108 = l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_Simp___hyg_6_(x_104, x_5, x_6, x_61, x_8, x_105);
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
x_11 = x_110;
x_12 = x_6;
x_13 = x_104;
x_14 = x_5;
x_15 = x_4;
x_16 = x_109;
x_17 = x_108;
x_18 = x_3;
x_19 = x_61;
x_20 = x_112;
goto block_35;
}
else
{
x_10 = x_8;
x_11 = x_110;
x_12 = x_6;
x_13 = x_104;
x_14 = x_5;
x_15 = x_4;
x_16 = x_109;
x_17 = x_108;
x_18 = x_3;
x_19 = x_61;
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
lean_ctor_set_uint8(x_123, sizeof(void*)*2 + 3, x_106);
lean_ctor_set_uint8(x_123, sizeof(void*)*2 + 4, x_106);
lean_ctor_set_uint8(x_123, sizeof(void*)*2 + 5, x_106);
x_124 = lean_unbox(x_122);
lean_ctor_set_uint8(x_123, sizeof(void*)*2 + 6, x_124);
lean_ctor_set_uint8(x_123, sizeof(void*)*2 + 7, x_106);
lean_ctor_set_uint8(x_123, sizeof(void*)*2 + 8, x_106);
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
x_153 = lean_mk_string_unchecked("Config", 6, 6);
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
x_175 = l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_Simp___hyg_6_(x_170, x_5, x_6, x_148, x_8, x_171);
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
x_11 = x_177;
x_12 = x_6;
x_13 = x_170;
x_14 = x_5;
x_15 = x_4;
x_16 = x_176;
x_17 = x_175;
x_18 = x_3;
x_19 = x_148;
x_20 = x_179;
goto block_35;
}
else
{
x_10 = x_8;
x_11 = x_177;
x_12 = x_6;
x_13 = x_170;
x_14 = x_5;
x_15 = x_4;
x_16 = x_176;
x_17 = x_175;
x_18 = x_3;
x_19 = x_148;
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
lean_ctor_set_uint8(x_190, sizeof(void*)*2 + 3, x_173);
lean_ctor_set_uint8(x_190, sizeof(void*)*2 + 4, x_173);
lean_ctor_set_uint8(x_190, sizeof(void*)*2 + 5, x_173);
x_191 = lean_unbox(x_189);
lean_ctor_set_uint8(x_190, sizeof(void*)*2 + 6, x_191);
lean_ctor_set_uint8(x_190, sizeof(void*)*2 + 7, x_173);
lean_ctor_set_uint8(x_190, sizeof(void*)*2 + 8, x_173);
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
x_205 = lean_unbox(x_40);
lean_ctor_set_uint8(x_201, sizeof(void*)*2 + 3, x_205);
x_206 = lean_unbox(x_40);
lean_ctor_set_uint8(x_201, sizeof(void*)*2 + 4, x_206);
x_207 = lean_unbox(x_40);
lean_ctor_set_uint8(x_201, sizeof(void*)*2 + 5, x_207);
x_208 = lean_unbox(x_200);
lean_ctor_set_uint8(x_201, sizeof(void*)*2 + 6, x_208);
x_209 = lean_unbox(x_40);
lean_ctor_set_uint8(x_201, sizeof(void*)*2 + 7, x_209);
x_210 = lean_unbox(x_40);
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
lean_dec(x_17);
x_21 = lean_mk_string_unchecked("error evaluating configuration\n", 31, 31);
x_22 = l_Lean_stringToMessageData(x_21);
lean_dec(x_21);
x_23 = l_Lean_MessageData_ofExpr(x_13);
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
x_29 = l_Lean_Exception_toMessageData(x_16);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_mk_string_unchecked("", 0, 0);
x_32 = l_Lean_stringToMessageData(x_31);
lean_dec(x_31);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_33, x_18, x_15, x_14, x_12, x_19, x_10, x_11);
lean_dec(x_10);
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_14);
lean_dec(x_15);
return x_34;
}
else
{
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_elabSimpConfigCore___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_elabSimpConfigCore___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_elabSimpConfigCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_Simp___hyg_576_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Meta", 4, 4);
x_9 = lean_mk_string_unchecked("Simp", 4, 4);
x_10 = lean_mk_string_unchecked("ConfigCtx", 9, 9);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
x_14 = l_Lean_Meta_evalExpr_x27(lean_box(0), x_11, x_1, x_13, x_2, x_3, x_4, x_5, x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_576_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_Simp___hyg_576_(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_576____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_576_(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCtxCore___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_66 = lean_mk_string_unchecked("ConfigCtx", 9, 9);
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
x_87 = l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_Simp___hyg_576_(x_83, x_5, x_6, x_61, x_8, x_84);
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
x_10 = x_89;
x_11 = x_8;
x_12 = x_4;
x_13 = x_61;
x_14 = x_5;
x_15 = x_3;
x_16 = x_6;
x_17 = x_87;
x_18 = x_83;
x_19 = x_88;
x_20 = x_91;
goto block_35;
}
else
{
x_10 = x_89;
x_11 = x_8;
x_12 = x_4;
x_13 = x_61;
x_14 = x_5;
x_15 = x_3;
x_16 = x_6;
x_17 = x_87;
x_18 = x_83;
x_19 = x_88;
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
lean_ctor_set_uint8(x_102, sizeof(void*)*2, x_85);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 1, x_85);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 2, x_39);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 3, x_85);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 4, x_85);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 5, x_85);
x_103 = lean_unbox(x_101);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 6, x_103);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 7, x_85);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 8, x_85);
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
x_108 = l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_Simp___hyg_576_(x_104, x_5, x_6, x_61, x_8, x_105);
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
x_10 = x_110;
x_11 = x_8;
x_12 = x_4;
x_13 = x_61;
x_14 = x_5;
x_15 = x_3;
x_16 = x_6;
x_17 = x_108;
x_18 = x_104;
x_19 = x_109;
x_20 = x_112;
goto block_35;
}
else
{
x_10 = x_110;
x_11 = x_8;
x_12 = x_4;
x_13 = x_61;
x_14 = x_5;
x_15 = x_3;
x_16 = x_6;
x_17 = x_108;
x_18 = x_104;
x_19 = x_109;
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
lean_ctor_set_uint8(x_123, sizeof(void*)*2, x_106);
lean_ctor_set_uint8(x_123, sizeof(void*)*2 + 1, x_106);
lean_ctor_set_uint8(x_123, sizeof(void*)*2 + 2, x_39);
lean_ctor_set_uint8(x_123, sizeof(void*)*2 + 3, x_106);
lean_ctor_set_uint8(x_123, sizeof(void*)*2 + 4, x_106);
lean_ctor_set_uint8(x_123, sizeof(void*)*2 + 5, x_106);
x_124 = lean_unbox(x_122);
lean_ctor_set_uint8(x_123, sizeof(void*)*2 + 6, x_124);
lean_ctor_set_uint8(x_123, sizeof(void*)*2 + 7, x_106);
lean_ctor_set_uint8(x_123, sizeof(void*)*2 + 8, x_106);
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
x_153 = lean_mk_string_unchecked("ConfigCtx", 9, 9);
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
x_175 = l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_Simp___hyg_576_(x_170, x_5, x_6, x_148, x_8, x_171);
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
x_10 = x_177;
x_11 = x_8;
x_12 = x_4;
x_13 = x_148;
x_14 = x_5;
x_15 = x_3;
x_16 = x_6;
x_17 = x_175;
x_18 = x_170;
x_19 = x_176;
x_20 = x_179;
goto block_35;
}
else
{
x_10 = x_177;
x_11 = x_8;
x_12 = x_4;
x_13 = x_148;
x_14 = x_5;
x_15 = x_3;
x_16 = x_6;
x_17 = x_175;
x_18 = x_170;
x_19 = x_176;
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
lean_ctor_set_uint8(x_190, sizeof(void*)*2, x_173);
lean_ctor_set_uint8(x_190, sizeof(void*)*2 + 1, x_173);
lean_ctor_set_uint8(x_190, sizeof(void*)*2 + 2, x_39);
lean_ctor_set_uint8(x_190, sizeof(void*)*2 + 3, x_173);
lean_ctor_set_uint8(x_190, sizeof(void*)*2 + 4, x_173);
lean_ctor_set_uint8(x_190, sizeof(void*)*2 + 5, x_173);
x_191 = lean_unbox(x_189);
lean_ctor_set_uint8(x_190, sizeof(void*)*2 + 6, x_191);
lean_ctor_set_uint8(x_190, sizeof(void*)*2 + 7, x_173);
lean_ctor_set_uint8(x_190, sizeof(void*)*2 + 8, x_173);
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
x_202 = lean_unbox(x_40);
lean_ctor_set_uint8(x_201, sizeof(void*)*2, x_202);
x_203 = lean_unbox(x_40);
lean_ctor_set_uint8(x_201, sizeof(void*)*2 + 1, x_203);
x_204 = lean_unbox(x_199);
lean_ctor_set_uint8(x_201, sizeof(void*)*2 + 2, x_204);
x_205 = lean_unbox(x_40);
lean_ctor_set_uint8(x_201, sizeof(void*)*2 + 3, x_205);
x_206 = lean_unbox(x_40);
lean_ctor_set_uint8(x_201, sizeof(void*)*2 + 4, x_206);
x_207 = lean_unbox(x_40);
lean_ctor_set_uint8(x_201, sizeof(void*)*2 + 5, x_207);
x_208 = lean_unbox(x_200);
lean_ctor_set_uint8(x_201, sizeof(void*)*2 + 6, x_208);
x_209 = lean_unbox(x_40);
lean_ctor_set_uint8(x_201, sizeof(void*)*2 + 7, x_209);
x_210 = lean_unbox(x_40);
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
lean_dec(x_17);
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
x_29 = l_Lean_Exception_toMessageData(x_19);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_mk_string_unchecked("", 0, 0);
x_32 = l_Lean_stringToMessageData(x_31);
lean_dec(x_31);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_33, x_15, x_12, x_14, x_16, x_13, x_11, x_10);
lean_dec(x_11);
lean_dec(x_13);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
return x_34;
}
else
{
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCtxCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_elabSimpConfigCtxCore___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCtxCore___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_elabSimpConfigCtxCore___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCtxCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_elabSimpConfigCtxCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_Simp___hyg_1146_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Meta", 4, 4);
x_9 = lean_mk_string_unchecked("DSimp", 5, 5);
x_10 = lean_mk_string_unchecked("Config", 6, 6);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
x_14 = l_Lean_Meta_evalExpr_x27(lean_box(0), x_11, x_1, x_13, x_2, x_3, x_4, x_5, x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_1146_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_Simp___hyg_1146_(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_1146____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_1146_(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDSimpConfigCore___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_65 = lean_mk_string_unchecked("DSimp", 5, 5);
x_66 = lean_mk_string_unchecked("Config", 6, 6);
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
x_87 = l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_Simp___hyg_1146_(x_83, x_5, x_6, x_61, x_8, x_84);
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
x_10 = x_5;
x_11 = x_88;
x_12 = x_89;
x_13 = x_61;
x_14 = x_8;
x_15 = x_6;
x_16 = x_4;
x_17 = x_3;
x_18 = x_87;
x_19 = x_83;
x_20 = x_91;
goto block_35;
}
else
{
x_10 = x_5;
x_11 = x_88;
x_12 = x_89;
x_13 = x_61;
x_14 = x_8;
x_15 = x_6;
x_16 = x_4;
x_17 = x_3;
x_18 = x_87;
x_19 = x_83;
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
lean_object* x_99; lean_object* x_100; uint8_t x_101; 
lean_dec(x_83);
lean_dec(x_61);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_99 = lean_box(0);
x_100 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_100, 0, x_85);
lean_ctor_set_uint8(x_100, 1, x_85);
lean_ctor_set_uint8(x_100, 2, x_85);
x_101 = lean_unbox(x_99);
lean_ctor_set_uint8(x_100, 3, x_101);
lean_ctor_set_uint8(x_100, 4, x_85);
lean_ctor_set_uint8(x_100, 5, x_85);
lean_ctor_set_uint8(x_100, 6, x_39);
lean_ctor_set_uint8(x_100, 7, x_39);
lean_ctor_set_uint8(x_100, 8, x_85);
lean_ctor_set_uint8(x_100, 9, x_39);
lean_ctor_set_uint8(x_100, 10, x_39);
lean_ctor_set_uint8(x_100, 11, x_85);
lean_ctor_set_uint8(x_100, 12, x_85);
lean_ctor_set(x_81, 0, x_100);
return x_81;
}
}
else
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_102 = lean_ctor_get(x_81, 0);
x_103 = lean_ctor_get(x_81, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_81);
x_104 = l_Lean_Expr_hasSyntheticSorry(x_102);
if (x_104 == 0)
{
uint8_t x_105; 
x_105 = l_Lean_Expr_hasSorry(x_102);
if (x_105 == 0)
{
lean_object* x_106; 
lean_inc(x_8);
lean_inc(x_61);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_102);
x_106 = l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_Simp___hyg_1146_(x_102, x_5, x_6, x_61, x_8, x_103);
if (lean_obj_tag(x_106) == 0)
{
lean_dec(x_102);
lean_dec(x_61);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
x_109 = l_Lean_Exception_isInterrupt(x_107);
if (x_109 == 0)
{
uint8_t x_110; 
x_110 = l_Lean_Exception_isRuntime(x_107);
x_10 = x_5;
x_11 = x_107;
x_12 = x_108;
x_13 = x_61;
x_14 = x_8;
x_15 = x_6;
x_16 = x_4;
x_17 = x_3;
x_18 = x_106;
x_19 = x_102;
x_20 = x_110;
goto block_35;
}
else
{
x_10 = x_5;
x_11 = x_107;
x_12 = x_108;
x_13 = x_61;
x_14 = x_8;
x_15 = x_6;
x_16 = x_4;
x_17 = x_3;
x_18 = x_106;
x_19 = x_102;
x_20 = x_109;
goto block_35;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_102);
x_111 = lean_mk_string_unchecked("configuration contains 'sorry'", 30, 30);
x_112 = l_Lean_stringToMessageData(x_111);
lean_dec(x_111);
x_113 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_112, x_3, x_4, x_5, x_6, x_61, x_8, x_103);
lean_dec(x_8);
lean_dec(x_61);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_116 = x_113;
} else {
 lean_dec_ref(x_113);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; 
lean_dec(x_102);
lean_dec(x_61);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_118 = lean_box(0);
x_119 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_119, 0, x_104);
lean_ctor_set_uint8(x_119, 1, x_104);
lean_ctor_set_uint8(x_119, 2, x_104);
x_120 = lean_unbox(x_118);
lean_ctor_set_uint8(x_119, 3, x_120);
lean_ctor_set_uint8(x_119, 4, x_104);
lean_ctor_set_uint8(x_119, 5, x_104);
lean_ctor_set_uint8(x_119, 6, x_39);
lean_ctor_set_uint8(x_119, 7, x_39);
lean_ctor_set_uint8(x_119, 8, x_104);
lean_ctor_set_uint8(x_119, 9, x_39);
lean_ctor_set_uint8(x_119, 10, x_39);
lean_ctor_set_uint8(x_119, 11, x_104);
lean_ctor_set_uint8(x_119, 12, x_104);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_103);
return x_121;
}
}
}
else
{
uint8_t x_122; 
lean_dec(x_61);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_122 = !lean_is_exclusive(x_81);
if (x_122 == 0)
{
return x_81;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_81, 0);
x_124 = lean_ctor_get(x_81, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_81);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; uint8_t x_152; 
x_126 = lean_ctor_get(x_41, 0);
x_127 = lean_ctor_get(x_41, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_41);
x_128 = lean_ctor_get(x_7, 5);
x_129 = l_Lean_replaceRef(x_1, x_128);
lean_dec(x_1);
x_130 = lean_ctor_get(x_7, 0);
x_131 = lean_ctor_get(x_7, 1);
x_132 = lean_ctor_get(x_7, 2);
x_133 = lean_ctor_get(x_7, 3);
x_134 = lean_ctor_get(x_7, 4);
x_135 = lean_ctor_get(x_7, 6);
x_136 = lean_ctor_get(x_7, 7);
x_137 = lean_ctor_get(x_7, 8);
x_138 = lean_ctor_get(x_7, 9);
x_139 = lean_ctor_get(x_7, 10);
x_140 = lean_ctor_get_uint8(x_7, sizeof(void*)*13);
x_141 = lean_ctor_get(x_7, 11);
x_142 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_143 = lean_ctor_get(x_7, 12);
lean_inc(x_143);
lean_inc(x_141);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
x_144 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_144, 0, x_130);
lean_ctor_set(x_144, 1, x_131);
lean_ctor_set(x_144, 2, x_132);
lean_ctor_set(x_144, 3, x_133);
lean_ctor_set(x_144, 4, x_134);
lean_ctor_set(x_144, 5, x_129);
lean_ctor_set(x_144, 6, x_135);
lean_ctor_set(x_144, 7, x_136);
lean_ctor_set(x_144, 8, x_137);
lean_ctor_set(x_144, 9, x_138);
lean_ctor_set(x_144, 10, x_139);
lean_ctor_set(x_144, 11, x_141);
lean_ctor_set(x_144, 12, x_143);
lean_ctor_set_uint8(x_144, sizeof(void*)*13, x_140);
lean_ctor_set_uint8(x_144, sizeof(void*)*13 + 1, x_142);
x_145 = lean_ctor_get(x_126, 0);
lean_inc(x_145);
lean_dec(x_126);
x_146 = lean_mk_string_unchecked("Lean", 4, 4);
x_147 = lean_mk_string_unchecked("Meta", 4, 4);
x_148 = lean_mk_string_unchecked("DSimp", 5, 5);
x_149 = lean_mk_string_unchecked("Config", 6, 6);
x_150 = l_Lean_Name_mkStr4(x_146, x_147, x_148, x_149);
x_151 = lean_unbox(x_40);
lean_inc(x_150);
x_152 = l_Lean_Environment_contains(x_145, x_150, x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_38);
x_153 = lean_mk_string_unchecked("error evaluating configuration, environment does not yet contain type ", 70, 70);
x_154 = l_Lean_stringToMessageData(x_153);
lean_dec(x_153);
x_155 = l_Lean_MessageData_ofName(x_150);
x_156 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
x_157 = lean_mk_string_unchecked("", 0, 0);
x_158 = l_Lean_stringToMessageData(x_157);
lean_dec(x_157);
x_159 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_158);
x_160 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_159, x_3, x_4, x_5, x_6, x_144, x_8, x_127);
lean_dec(x_8);
lean_dec(x_144);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_163 = x_160;
} else {
 lean_dec_ref(x_160);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
else
{
lean_object* x_165; 
lean_inc(x_8);
lean_inc(x_144);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_165 = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_elabConfig(x_36, x_150, x_38, x_3, x_4, x_5, x_6, x_144, x_8, x_127);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_168 = x_165;
} else {
 lean_dec_ref(x_165);
 x_168 = lean_box(0);
}
x_169 = l_Lean_Expr_hasSyntheticSorry(x_166);
if (x_169 == 0)
{
uint8_t x_170; 
lean_dec(x_168);
x_170 = l_Lean_Expr_hasSorry(x_166);
if (x_170 == 0)
{
lean_object* x_171; 
lean_inc(x_8);
lean_inc(x_144);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_166);
x_171 = l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_Simp___hyg_1146_(x_166, x_5, x_6, x_144, x_8, x_167);
if (lean_obj_tag(x_171) == 0)
{
lean_dec(x_166);
lean_dec(x_144);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_171;
}
else
{
lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
x_174 = l_Lean_Exception_isInterrupt(x_172);
if (x_174 == 0)
{
uint8_t x_175; 
x_175 = l_Lean_Exception_isRuntime(x_172);
x_10 = x_5;
x_11 = x_172;
x_12 = x_173;
x_13 = x_144;
x_14 = x_8;
x_15 = x_6;
x_16 = x_4;
x_17 = x_3;
x_18 = x_171;
x_19 = x_166;
x_20 = x_175;
goto block_35;
}
else
{
x_10 = x_5;
x_11 = x_172;
x_12 = x_173;
x_13 = x_144;
x_14 = x_8;
x_15 = x_6;
x_16 = x_4;
x_17 = x_3;
x_18 = x_171;
x_19 = x_166;
x_20 = x_174;
goto block_35;
}
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_166);
x_176 = lean_mk_string_unchecked("configuration contains 'sorry'", 30, 30);
x_177 = l_Lean_stringToMessageData(x_176);
lean_dec(x_176);
x_178 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_177, x_3, x_4, x_5, x_6, x_144, x_8, x_167);
lean_dec(x_8);
lean_dec(x_144);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_181 = x_178;
} else {
 lean_dec_ref(x_178);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_179);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
}
else
{
lean_object* x_183; lean_object* x_184; uint8_t x_185; lean_object* x_186; 
lean_dec(x_166);
lean_dec(x_144);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_183 = lean_box(0);
x_184 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_184, 0, x_169);
lean_ctor_set_uint8(x_184, 1, x_169);
lean_ctor_set_uint8(x_184, 2, x_169);
x_185 = lean_unbox(x_183);
lean_ctor_set_uint8(x_184, 3, x_185);
lean_ctor_set_uint8(x_184, 4, x_169);
lean_ctor_set_uint8(x_184, 5, x_169);
lean_ctor_set_uint8(x_184, 6, x_39);
lean_ctor_set_uint8(x_184, 7, x_39);
lean_ctor_set_uint8(x_184, 8, x_169);
lean_ctor_set_uint8(x_184, 9, x_39);
lean_ctor_set_uint8(x_184, 10, x_39);
lean_ctor_set_uint8(x_184, 11, x_169);
lean_ctor_set_uint8(x_184, 12, x_169);
if (lean_is_scalar(x_168)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_168;
}
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_167);
return x_186;
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_144);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_187 = lean_ctor_get(x_165, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_165, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_189 = x_165;
} else {
 lean_dec_ref(x_165);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(1, 2, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_187);
lean_ctor_set(x_190, 1, x_188);
return x_190;
}
}
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; uint8_t x_195; uint8_t x_196; uint8_t x_197; uint8_t x_198; uint8_t x_199; uint8_t x_200; uint8_t x_201; uint8_t x_202; uint8_t x_203; uint8_t x_204; uint8_t x_205; uint8_t x_206; lean_object* x_207; 
lean_dec(x_38);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_191 = lean_box(0);
x_192 = lean_box(0);
x_193 = lean_alloc_ctor(0, 0, 13);
x_194 = lean_unbox(x_40);
lean_ctor_set_uint8(x_193, 0, x_194);
x_195 = lean_unbox(x_40);
lean_ctor_set_uint8(x_193, 1, x_195);
x_196 = lean_unbox(x_40);
lean_ctor_set_uint8(x_193, 2, x_196);
x_197 = lean_unbox(x_191);
lean_ctor_set_uint8(x_193, 3, x_197);
x_198 = lean_unbox(x_40);
lean_ctor_set_uint8(x_193, 4, x_198);
x_199 = lean_unbox(x_40);
lean_ctor_set_uint8(x_193, 5, x_199);
x_200 = lean_unbox(x_192);
lean_ctor_set_uint8(x_193, 6, x_200);
x_201 = lean_unbox(x_192);
lean_ctor_set_uint8(x_193, 7, x_201);
x_202 = lean_unbox(x_40);
lean_ctor_set_uint8(x_193, 8, x_202);
x_203 = lean_unbox(x_192);
lean_ctor_set_uint8(x_193, 9, x_203);
x_204 = lean_unbox(x_192);
lean_ctor_set_uint8(x_193, 10, x_204);
x_205 = lean_unbox(x_40);
lean_ctor_set_uint8(x_193, 11, x_205);
x_206 = lean_unbox(x_40);
lean_ctor_set_uint8(x_193, 12, x_206);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_193);
lean_ctor_set(x_207, 1, x_9);
return x_207;
}
block_35:
{
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_18);
x_21 = lean_mk_string_unchecked("error evaluating configuration\n", 31, 31);
x_22 = l_Lean_stringToMessageData(x_21);
lean_dec(x_21);
x_23 = l_Lean_MessageData_ofExpr(x_19);
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
x_29 = l_Lean_Exception_toMessageData(x_11);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_mk_string_unchecked("", 0, 0);
x_32 = l_Lean_stringToMessageData(x_31);
lean_dec(x_31);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_33, x_17, x_16, x_10, x_15, x_13, x_14, x_12);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_16);
return x_34;
}
else
{
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDSimpConfigCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_elabDSimpConfigCore___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDSimpConfigCore___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_elabDSimpConfigCore___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDSimpConfigCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_elabDSimpConfigCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SimpKind_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SimpKind_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Elab_Tactic_SimpKind_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SimpKind_noConfusion___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SimpKind_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_SimpKind_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SimpKind_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_SimpKind_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SimpKind_noConfusion___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_SimpKind_noConfusion___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SimpKind_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Elab_Tactic_SimpKind_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SimpKind_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Elab_Tactic_SimpKind_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_instInhabitedSimpKind() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_unbox(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_beqSimpKind____x40_Lean_Elab_Tactic_Simp___hyg_1730_(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Elab_Tactic_SimpKind_toCtorIdx(x_1);
x_4 = l_Lean_Elab_Tactic_SimpKind_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_beqSimpKind____x40_Lean_Elab_Tactic_Simp___hyg_1730____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_beqSimpKind____x40_Lean_Elab_Tactic_Simp___hyg_1730_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instBEqSimpKind() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_beqSimpKind____x40_Lean_Elab_Tactic_Simp___hyg_1730____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticToDischarge___redArg___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_7);
x_11 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_3, x_7, x_12);
lean_dec(x_7);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Lean_Expr_hasExprMVar(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; 
lean_dec(x_15);
x_18 = lean_box(0);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = l_Lean_Expr_hasExprMVar(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_19);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_7);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_11);
if (x_26 == 0)
{
return x_11;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_11, 0);
x_28 = lean_ctor_get(x_11, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_11);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticToDischarge___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo(lean_box(0), x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_20; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_20 = l_Lean_Exception_isInterrupt(x_10);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = l_Lean_Exception_isRuntime(x_10);
lean_dec(x_10);
x_12 = x_21;
goto block_19;
}
else
{
lean_dec(x_10);
x_12 = x_20;
goto block_19;
}
block_19:
{
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_dec(x_14);
x_15 = lean_ctor_get(x_9, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set_tag(x_9, 0);
lean_ctor_set(x_9, 0, x_16);
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_11);
return x_18;
}
}
else
{
lean_dec(x_11);
return x_9;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticToDischarge___redArg___lam__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_14 = lean_mk_string_unchecked("simp", 4, 4);
x_15 = lean_mk_string_unchecked("discharger", 10, 10);
x_16 = l_Lean_Name_mkStr2(x_14, x_15);
lean_inc(x_9);
x_17 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_5, x_16, x_9, x_10, x_11, x_12, x_13);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_1, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Expr_mvarId_x21(x_18);
x_24 = lean_box(0);
x_25 = lean_box(x_3);
x_26 = lean_alloc_closure((void*)(l_Lean_Elab_Term_runTactic___boxed), 11, 4);
lean_closure_set(x_26, 0, x_23);
lean_closure_set(x_26, 1, x_2);
lean_closure_set(x_26, 2, x_24);
lean_closure_set(x_26, 3, x_25);
x_27 = lean_box(1);
x_28 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_tacticToDischarge___redArg___lam__0___boxed), 10, 3);
lean_closure_set(x_28, 0, x_26);
lean_closure_set(x_28, 1, x_27);
lean_closure_set(x_28, 2, x_18);
x_29 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_tacticToDischarge___redArg___lam__1), 8, 1);
lean_closure_set(x_29, 0, x_28);
x_30 = l_Lean_Elab_Term_TermElabM_run___redArg(x_29, x_4, x_21, x_9, x_10, x_11, x_12, x_22);
lean_dec(x_9);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_st_ref_set(x_1, x_34, x_32);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_33);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_30);
if (x_40 == 0)
{
return x_30;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_30, 0);
x_42 = lean_ctor_get(x_30, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_30);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticToDischarge___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_4, 5);
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
x_14 = l_Lean_SourceInfo_fromRef(x_11, x_13);
x_15 = lean_mk_string_unchecked("Lean", 4, 4);
x_16 = lean_mk_string_unchecked("Parser", 6, 6);
x_17 = lean_mk_string_unchecked("Tactic", 6, 6);
x_18 = lean_mk_string_unchecked("tacticSeq", 9, 9);
x_19 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_20 = l_Lean_Name_mkStr4(x_15, x_16, x_17, x_19);
x_21 = lean_mk_string_unchecked("null", 4, 4);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_24 = l_Lean_Name_mkStr4(x_15, x_16, x_17, x_23);
x_25 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_14);
lean_ctor_set_tag(x_7, 2);
lean_ctor_set(x_7, 1, x_25);
lean_ctor_set(x_7, 0, x_14);
x_26 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_14);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_26);
lean_inc(x_14);
x_28 = l_Lean_Syntax_node3(x_14, x_24, x_7, x_1, x_27);
lean_inc(x_14);
x_29 = l_Lean_Syntax_node1(x_14, x_22, x_28);
x_30 = lean_st_ref_get(x_3, x_9);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
x_34 = lean_st_mk_ref(x_32, x_33);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_mk_string_unchecked("tacticTry_", 10, 10);
x_38 = lean_mk_string_unchecked("try", 3, 3);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_39 = l_Lean_Name_mkStr4(x_15, x_16, x_17, x_18);
lean_inc(x_14);
x_40 = l_Lean_Syntax_node1(x_14, x_20, x_29);
x_41 = l_Lean_Name_mkStr4(x_15, x_16, x_17, x_37);
lean_inc(x_14);
lean_ctor_set_tag(x_30, 2);
lean_ctor_set(x_30, 1, x_38);
lean_ctor_set(x_30, 0, x_14);
lean_inc(x_14);
x_42 = l_Lean_Syntax_node1(x_14, x_39, x_40);
x_43 = l_Lean_Syntax_node2(x_14, x_41, x_30, x_42);
lean_inc(x_36);
x_44 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_tacticToDischarge___redArg___lam__2___boxed), 13, 4);
lean_closure_set(x_44, 0, x_36);
lean_closure_set(x_44, 1, x_43);
lean_closure_set(x_44, 2, x_12);
lean_closure_set(x_44, 3, x_2);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_36);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_34, 0, x_45);
return x_34;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_46 = lean_ctor_get(x_34, 0);
x_47 = lean_ctor_get(x_34, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_34);
x_48 = lean_mk_string_unchecked("tacticTry_", 10, 10);
x_49 = lean_mk_string_unchecked("try", 3, 3);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_50 = l_Lean_Name_mkStr4(x_15, x_16, x_17, x_18);
lean_inc(x_14);
x_51 = l_Lean_Syntax_node1(x_14, x_20, x_29);
x_52 = l_Lean_Name_mkStr4(x_15, x_16, x_17, x_48);
lean_inc(x_14);
lean_ctor_set_tag(x_30, 2);
lean_ctor_set(x_30, 1, x_49);
lean_ctor_set(x_30, 0, x_14);
lean_inc(x_14);
x_53 = l_Lean_Syntax_node1(x_14, x_50, x_51);
x_54 = l_Lean_Syntax_node2(x_14, x_52, x_30, x_53);
lean_inc(x_46);
x_55 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_tacticToDischarge___redArg___lam__2___boxed), 13, 4);
lean_closure_set(x_55, 0, x_46);
lean_closure_set(x_55, 1, x_54);
lean_closure_set(x_55, 2, x_12);
lean_closure_set(x_55, 3, x_2);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_46);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_47);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_58 = lean_ctor_get(x_30, 0);
x_59 = lean_ctor_get(x_30, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_30);
x_60 = lean_st_mk_ref(x_58, x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
x_64 = lean_mk_string_unchecked("tacticTry_", 10, 10);
x_65 = lean_mk_string_unchecked("try", 3, 3);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_66 = l_Lean_Name_mkStr4(x_15, x_16, x_17, x_18);
lean_inc(x_14);
x_67 = l_Lean_Syntax_node1(x_14, x_20, x_29);
x_68 = l_Lean_Name_mkStr4(x_15, x_16, x_17, x_64);
lean_inc(x_14);
x_69 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_69, 0, x_14);
lean_ctor_set(x_69, 1, x_65);
lean_inc(x_14);
x_70 = l_Lean_Syntax_node1(x_14, x_66, x_67);
x_71 = l_Lean_Syntax_node2(x_14, x_68, x_69, x_70);
lean_inc(x_61);
x_72 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_tacticToDischarge___redArg___lam__2___boxed), 13, 4);
lean_closure_set(x_72, 0, x_61);
lean_closure_set(x_72, 1, x_71);
lean_closure_set(x_72, 2, x_12);
lean_closure_set(x_72, 3, x_2);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_61);
lean_ctor_set(x_73, 1, x_72);
if (lean_is_scalar(x_63)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_63;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_62);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_75 = lean_ctor_get(x_7, 1);
lean_inc(x_75);
lean_dec(x_7);
x_76 = lean_ctor_get(x_4, 5);
x_77 = lean_box(0);
x_78 = lean_unbox(x_77);
x_79 = l_Lean_SourceInfo_fromRef(x_76, x_78);
x_80 = lean_mk_string_unchecked("Lean", 4, 4);
x_81 = lean_mk_string_unchecked("Parser", 6, 6);
x_82 = lean_mk_string_unchecked("Tactic", 6, 6);
x_83 = lean_mk_string_unchecked("tacticSeq", 9, 9);
x_84 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
x_85 = l_Lean_Name_mkStr4(x_80, x_81, x_82, x_84);
x_86 = lean_mk_string_unchecked("null", 4, 4);
x_87 = l_Lean_Name_mkStr1(x_86);
x_88 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
x_89 = l_Lean_Name_mkStr4(x_80, x_81, x_82, x_88);
x_90 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_79);
x_91 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_91, 0, x_79);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_79);
x_93 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_93, 0, x_79);
lean_ctor_set(x_93, 1, x_92);
lean_inc(x_79);
x_94 = l_Lean_Syntax_node3(x_79, x_89, x_91, x_1, x_93);
lean_inc(x_79);
x_95 = l_Lean_Syntax_node1(x_79, x_87, x_94);
x_96 = lean_st_ref_get(x_3, x_75);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_99 = x_96;
} else {
 lean_dec_ref(x_96);
 x_99 = lean_box(0);
}
x_100 = lean_st_mk_ref(x_97, x_98);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_103 = x_100;
} else {
 lean_dec_ref(x_100);
 x_103 = lean_box(0);
}
x_104 = lean_mk_string_unchecked("tacticTry_", 10, 10);
x_105 = lean_mk_string_unchecked("try", 3, 3);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
x_106 = l_Lean_Name_mkStr4(x_80, x_81, x_82, x_83);
lean_inc(x_79);
x_107 = l_Lean_Syntax_node1(x_79, x_85, x_95);
x_108 = l_Lean_Name_mkStr4(x_80, x_81, x_82, x_104);
lean_inc(x_79);
if (lean_is_scalar(x_99)) {
 x_109 = lean_alloc_ctor(2, 2, 0);
} else {
 x_109 = x_99;
 lean_ctor_set_tag(x_109, 2);
}
lean_ctor_set(x_109, 0, x_79);
lean_ctor_set(x_109, 1, x_105);
lean_inc(x_79);
x_110 = l_Lean_Syntax_node1(x_79, x_106, x_107);
x_111 = l_Lean_Syntax_node2(x_79, x_108, x_109, x_110);
lean_inc(x_101);
x_112 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_tacticToDischarge___redArg___lam__2___boxed), 13, 4);
lean_closure_set(x_112, 0, x_101);
lean_closure_set(x_112, 1, x_111);
lean_closure_set(x_112, 2, x_77);
lean_closure_set(x_112, 3, x_2);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_101);
lean_ctor_set(x_113, 1, x_112);
if (lean_is_scalar(x_103)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_103;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_102);
return x_114;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticToDischarge(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_tacticToDischarge___redArg(x_1, x_4, x_5, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticToDischarge___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_Elab_Tactic_tacticToDischarge___redArg___lam__0(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticToDischarge___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_Elab_Tactic_tacticToDischarge___redArg___lam__2(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticToDischarge___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_tacticToDischarge___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticToDischarge___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_tacticToDischarge(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_st_ref_get(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_st_ref_set(x_2, x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_apply_10(x_2, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_st_ref_get(x_6, x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_set(x_14, x_17, x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_15);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_15);
lean_inc(x_6);
x_22 = lean_apply_10(x_2, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
x_26 = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg___lam__0(x_14, x_6, x_25, x_24);
lean_dec(x_25);
lean_dec(x_6);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_23);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_22, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_dec(x_22);
x_33 = lean_box(0);
x_34 = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg___lam__0(x_14, x_6, x_33, x_32);
lean_dec(x_6);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 0, x_31);
return x_34;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_31);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_mkDischargeWrapper___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_Syntax_isNone(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(3u);
x_11 = l_Lean_Syntax_getArg(x_9, x_10);
lean_dec(x_9);
x_12 = l_Lean_Elab_Tactic_tacticToDischarge___redArg(x_11, x_2, x_3, x_4, x_5, x_6);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_ctor_set_tag(x_14, 1);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_12, 0, x_18);
return x_12;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_23 = x_19;
} else {
 lean_dec_ref(x_19);
 x_23 = lean_box(0);
}
if (lean_is_scalar(x_23)) {
 x_24 = lean_alloc_ctor(1, 2, 0);
} else {
 x_24 = x_23;
 lean_ctor_set_tag(x_24, 1);
}
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_2);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_6);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_mkDischargeWrapper(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_mkDischargeWrapper___redArg(x_1, x_4, x_5, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_mkDischargeWrapper___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_mkDischargeWrapper___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_mkDischargeWrapper___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_mkDischargeWrapper(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfig___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (x_2) {
case 0:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_elabSimpConfigCore___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
case 1:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_elabSimpConfigCtxCore___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
default: 
{
lean_object* x_21; 
x_21 = l_Lean_Elab_Tactic_elabDSimpConfigCore___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_unsigned_to_nat(100000u);
x_25 = lean_unsigned_to_nat(2u);
x_26 = lean_box(0);
x_27 = lean_box(1);
x_28 = lean_ctor_get_uint8(x_23, 0);
x_29 = lean_ctor_get_uint8(x_23, 1);
x_30 = lean_ctor_get_uint8(x_23, 2);
x_31 = lean_ctor_get_uint8(x_23, 3);
x_32 = lean_ctor_get_uint8(x_23, 4);
x_33 = lean_ctor_get_uint8(x_23, 5);
x_34 = lean_ctor_get_uint8(x_23, 6);
x_35 = lean_ctor_get_uint8(x_23, 7);
x_36 = lean_ctor_get_uint8(x_23, 8);
x_37 = lean_ctor_get_uint8(x_23, 9);
x_38 = lean_ctor_get_uint8(x_23, 10);
x_39 = lean_ctor_get_uint8(x_23, 11);
x_40 = lean_ctor_get_uint8(x_23, 12);
lean_dec(x_23);
x_41 = lean_alloc_ctor(0, 2, 20);
lean_ctor_set(x_41, 0, x_24);
lean_ctor_set(x_41, 1, x_25);
x_42 = lean_unbox(x_26);
lean_ctor_set_uint8(x_41, sizeof(void*)*2, x_42);
x_43 = lean_unbox(x_27);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 1, x_43);
x_44 = lean_unbox(x_26);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 2, x_44);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 3, x_28);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 4, x_29);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 5, x_30);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 6, x_31);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 7, x_32);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 8, x_33);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 9, x_34);
x_45 = lean_unbox(x_26);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 10, x_45);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 11, x_35);
x_46 = lean_unbox(x_27);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 12, x_46);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 13, x_36);
x_47 = lean_unbox(x_26);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 14, x_47);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 15, x_37);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 16, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 17, x_39);
x_48 = lean_unbox(x_27);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 18, x_48);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 19, x_40);
lean_ctor_set(x_21, 0, x_41);
return x_21;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; lean_object* x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; lean_object* x_76; 
x_49 = lean_ctor_get(x_21, 0);
x_50 = lean_ctor_get(x_21, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_21);
x_51 = lean_unsigned_to_nat(100000u);
x_52 = lean_unsigned_to_nat(2u);
x_53 = lean_box(0);
x_54 = lean_box(1);
x_55 = lean_ctor_get_uint8(x_49, 0);
x_56 = lean_ctor_get_uint8(x_49, 1);
x_57 = lean_ctor_get_uint8(x_49, 2);
x_58 = lean_ctor_get_uint8(x_49, 3);
x_59 = lean_ctor_get_uint8(x_49, 4);
x_60 = lean_ctor_get_uint8(x_49, 5);
x_61 = lean_ctor_get_uint8(x_49, 6);
x_62 = lean_ctor_get_uint8(x_49, 7);
x_63 = lean_ctor_get_uint8(x_49, 8);
x_64 = lean_ctor_get_uint8(x_49, 9);
x_65 = lean_ctor_get_uint8(x_49, 10);
x_66 = lean_ctor_get_uint8(x_49, 11);
x_67 = lean_ctor_get_uint8(x_49, 12);
lean_dec(x_49);
x_68 = lean_alloc_ctor(0, 2, 20);
lean_ctor_set(x_68, 0, x_51);
lean_ctor_set(x_68, 1, x_52);
x_69 = lean_unbox(x_53);
lean_ctor_set_uint8(x_68, sizeof(void*)*2, x_69);
x_70 = lean_unbox(x_54);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 1, x_70);
x_71 = lean_unbox(x_53);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 2, x_71);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 3, x_55);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 4, x_56);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 5, x_57);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 6, x_58);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 7, x_59);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 8, x_60);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 9, x_61);
x_72 = lean_unbox(x_53);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 10, x_72);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 11, x_62);
x_73 = lean_unbox(x_54);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 12, x_73);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 13, x_63);
x_74 = lean_unbox(x_53);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 14, x_74);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 15, x_64);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 16, x_65);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 17, x_66);
x_75 = lean_unbox(x_54);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 18, x_75);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 19, x_67);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_68);
lean_ctor_set(x_76, 1, x_50);
return x_76;
}
}
else
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_21);
if (x_77 == 0)
{
return x_21;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_21, 0);
x_79 = lean_ctor_get(x_21, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_21);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfig(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_elabSimpConfig___redArg(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfig___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_Elab_Tactic_elabSimpConfig___redArg(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfig___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Elab_Tactic_elabSimpConfig(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = l_Lean_Expr_isConst(x_4);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Expr_isFVar(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_mk_empty_array_with_capacity(x_15);
x_17 = lean_unsigned_to_nat(1000u);
x_18 = l_Lean_Meta_SimpTheorems_add(x_2, x_3, x_16, x_4, x_6, x_5, x_17, x_1, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_32; 
x_19 = l_Lean_Expr_fvarId_x21(x_4);
lean_inc(x_8);
lean_inc(x_19);
x_32 = l_Lean_FVarId_getDecl___redArg(x_19, x_8, x_10, x_11, x_12);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_54; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_54 = lean_ctor_get(x_33, 3);
lean_inc(x_54);
x_35 = x_54;
goto block_53;
block_53:
{
lean_object* x_36; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_36 = l_Lean_Meta_isProp(x_35, x_8, x_9, x_10, x_11, x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
lean_dec(x_3);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l_Lean_LocalDecl_isLet(x_33);
lean_dec(x_33);
if (x_40 == 0)
{
if (x_14 == 0)
{
x_20 = x_39;
goto block_31;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_19);
lean_dec(x_4);
lean_dec(x_2);
x_41 = lean_mk_string_unchecked("invalid argument, variable is not a proposition or let-declaration", 66, 66);
x_42 = l_Lean_stringToMessageData(x_41);
lean_dec(x_41);
x_43 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_42, x_8, x_9, x_10, x_11, x_39);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_43;
}
}
else
{
x_20 = x_39;
goto block_31;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_33);
lean_dec(x_19);
x_44 = lean_ctor_get(x_36, 1);
lean_inc(x_44);
lean_dec(x_36);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_mk_empty_array_with_capacity(x_45);
x_47 = lean_unsigned_to_nat(1000u);
x_48 = l_Lean_Meta_SimpTheorems_add(x_2, x_3, x_46, x_4, x_6, x_5, x_47, x_1, x_8, x_9, x_10, x_11, x_44);
lean_dec(x_8);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_33);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_36);
if (x_49 == 0)
{
return x_36;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_36, 0);
x_51 = lean_ctor_get(x_36, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_36);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_32);
if (x_55 == 0)
{
return x_32;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_32, 0);
x_57 = lean_ctor_get(x_32, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_32);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
block_31:
{
if (x_6 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_21 = l_Lean_Meta_SimpTheorems_addLetDeclToUnfold(x_2, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_19);
lean_dec(x_2);
x_23 = lean_mk_string_unchecked("invalid '←' modifier, '", 25, 23);
x_24 = l_Lean_stringToMessageData(x_23);
lean_dec(x_23);
x_25 = l_Lean_MessageData_ofExpr(x_4);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_mk_string_unchecked("' is a let-declaration name to be unfolded", 42, 42);
x_28 = l_Lean_stringToMessageData(x_27);
lean_dec(x_27);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_29, x_8, x_9, x_10, x_11, x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_30;
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_3);
x_59 = l_Lean_Expr_constName_x21(x_4);
lean_dec(x_4);
lean_inc(x_59);
x_60 = l_Lean_getConstVal___at___Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1_spec__1(x_59, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_ctor_get(x_61, 2);
lean_inc(x_63);
lean_dec(x_61);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_64 = l_Lean_Meta_isProp(x_63, x_8, x_9, x_10, x_11, x_62);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_unbox(x_65);
lean_dec(x_65);
if (x_66 == 0)
{
if (x_6 == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_64);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_72; 
x_68 = lean_ctor_get(x_64, 1);
x_69 = lean_ctor_get(x_64, 0);
lean_dec(x_69);
x_70 = lean_box(2);
x_71 = lean_unbox(x_70);
x_72 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_beqSimpKind____x40_Lean_Elab_Tactic_Simp___hyg_1730_(x_7, x_71);
if (x_72 == 0)
{
lean_object* x_73; 
lean_free_object(x_64);
x_73 = l_Lean_Meta_SimpTheorems_addDeclToUnfold(x_2, x_59, x_8, x_9, x_10, x_11, x_68);
lean_dec(x_8);
return x_73;
}
else
{
lean_object* x_74; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_74 = l_Lean_Meta_SimpTheorems_addDeclToUnfoldCore(x_2, x_59);
lean_ctor_set(x_64, 0, x_74);
return x_64;
}
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; uint8_t x_78; 
x_75 = lean_ctor_get(x_64, 1);
lean_inc(x_75);
lean_dec(x_64);
x_76 = lean_box(2);
x_77 = lean_unbox(x_76);
x_78 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_beqSimpKind____x40_Lean_Elab_Tactic_Simp___hyg_1730_(x_7, x_77);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = l_Lean_Meta_SimpTheorems_addDeclToUnfold(x_2, x_59, x_8, x_9, x_10, x_11, x_75);
lean_dec(x_8);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_80 = l_Lean_Meta_SimpTheorems_addDeclToUnfoldCore(x_2, x_59);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_75);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
lean_dec(x_2);
x_82 = lean_ctor_get(x_64, 1);
lean_inc(x_82);
lean_dec(x_64);
x_83 = lean_mk_string_unchecked("invalid '←' modifier, '", 25, 23);
x_84 = l_Lean_stringToMessageData(x_83);
lean_dec(x_83);
x_85 = l_Lean_MessageData_ofName(x_59);
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_mk_string_unchecked("' is a declaration name to be unfolded", 38, 38);
x_88 = l_Lean_stringToMessageData(x_87);
lean_dec(x_87);
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_88);
x_90 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_89, x_8, x_9, x_10, x_11, x_82);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
return x_90;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_90, 0);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_90);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_64, 1);
lean_inc(x_95);
lean_dec(x_64);
x_96 = lean_unsigned_to_nat(1000u);
x_97 = l_Lean_Meta_SimpTheorems_addConst(x_2, x_59, x_5, x_6, x_96, x_8, x_9, x_10, x_11, x_95);
lean_dec(x_8);
return x_97;
}
}
else
{
uint8_t x_98; 
lean_dec(x_59);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_98 = !lean_is_exclusive(x_64);
if (x_98 == 0)
{
return x_64;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_64, 0);
x_100 = lean_ctor_get(x_64, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_64);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_59);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_102 = !lean_is_exclusive(x_60);
if (x_102 == 0)
{
return x_60;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_60, 0);
x_104 = lean_ctor_get(x_60, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_60);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = lean_unbox(x_6);
lean_dec(x_6);
x_15 = lean_unbox(x_7);
lean_dec(x_7);
x_16 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem(x_1, x_2, x_3, x_4, x_13, x_14, x_15, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addSimpTheorem___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_11 = lean_ctor_get(x_8, 5);
x_12 = l_Lean_replaceRef(x_1, x_11);
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
x_15 = lean_ctor_get(x_8, 2);
x_16 = lean_ctor_get(x_8, 3);
x_17 = lean_ctor_get(x_8, 4);
x_18 = lean_ctor_get(x_8, 6);
x_19 = lean_ctor_get(x_8, 7);
x_20 = lean_ctor_get(x_8, 8);
x_21 = lean_ctor_get(x_8, 9);
x_22 = lean_ctor_get(x_8, 10);
x_23 = lean_ctor_get_uint8(x_8, sizeof(void*)*13);
x_24 = lean_ctor_get(x_8, 11);
x_25 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_26 = lean_ctor_get(x_8, 12);
lean_inc(x_26);
lean_inc(x_24);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_27 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_27, 0, x_13);
lean_ctor_set(x_27, 1, x_14);
lean_ctor_set(x_27, 2, x_15);
lean_ctor_set(x_27, 3, x_16);
lean_ctor_set(x_27, 4, x_17);
lean_ctor_set(x_27, 5, x_12);
lean_ctor_set(x_27, 6, x_18);
lean_ctor_set(x_27, 7, x_19);
lean_ctor_set(x_27, 8, x_20);
lean_ctor_set(x_27, 9, x_21);
lean_ctor_set(x_27, 10, x_22);
lean_ctor_set(x_27, 11, x_24);
lean_ctor_set(x_27, 12, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*13, x_23);
lean_ctor_set_uint8(x_27, sizeof(void*)*13 + 1, x_25);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_28 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_3, x_3, x_4, x_5, x_6, x_7, x_27, x_9, x_10);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_box(1);
x_32 = lean_unbox(x_31);
lean_inc(x_9);
lean_inc(x_27);
lean_inc(x_7);
lean_inc(x_6);
x_33 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_32, x_3, x_4, x_5, x_6, x_7, x_27, x_9, x_30);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_29, x_7, x_34);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
x_39 = l_Lean_Expr_hasSyntheticSorry(x_37);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = l_Lean_Expr_eta(x_37);
x_41 = l_Lean_Expr_hasMVar(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_mk_empty_array_with_capacity(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_35, 0, x_45);
return x_35;
}
else
{
lean_object* x_46; uint8_t x_47; 
lean_free_object(x_35);
x_46 = l_Lean_Meta_abstractMVars(x_40, x_3, x_6, x_7, x_27, x_9, x_38);
lean_dec(x_9);
lean_dec(x_27);
lean_dec(x_7);
lean_dec(x_6);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 2);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_46, 0, x_52);
return x_46;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_53 = lean_ctor_get(x_46, 0);
x_54 = lean_ctor_get(x_46, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_46);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_53, 2);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_54);
return x_59;
}
}
}
else
{
lean_object* x_60; 
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_60 = lean_box(0);
lean_ctor_set(x_35, 0, x_60);
return x_35;
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_35, 0);
x_62 = lean_ctor_get(x_35, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_35);
x_63 = l_Lean_Expr_hasSyntheticSorry(x_61);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = l_Lean_Expr_eta(x_61);
x_65 = l_Lean_Expr_hasMVar(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_66 = lean_unsigned_to_nat(0u);
x_67 = lean_mk_empty_array_with_capacity(x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_64);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_62);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_71 = l_Lean_Meta_abstractMVars(x_64, x_3, x_6, x_7, x_27, x_9, x_62);
lean_dec(x_9);
lean_dec(x_27);
lean_dec(x_7);
lean_dec(x_6);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_74 = x_71;
} else {
 lean_dec_ref(x_71);
 x_74 = lean_box(0);
}
x_75 = lean_ctor_get(x_72, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_72, 2);
lean_inc(x_76);
lean_dec(x_72);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
if (lean_is_scalar(x_74)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_74;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_73);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_61);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_62);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_82 = !lean_is_exclusive(x_33);
if (x_82 == 0)
{
return x_33;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_33, 0);
x_84 = lean_ctor_get(x_33, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_33);
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
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_86 = !lean_is_exclusive(x_28);
if (x_86 == 0)
{
return x_28;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_28, 0);
x_88 = lean_ctor_get(x_28, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_28);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addSimpTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_box(0);
x_15 = lean_box(1);
x_16 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addSimpTheorem___lam__0___boxed), 10, 3);
lean_closure_set(x_16, 0, x_4);
lean_closure_set(x_16, 1, x_14);
lean_closure_set(x_16, 2, x_15);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_17 = l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo(lean_box(0), x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
lean_ctor_set(x_17, 0, x_2);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_dec(x_17);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_unsigned_to_nat(1000u);
x_28 = l_Lean_Meta_SimpTheorems_add(x_2, x_3, x_25, x_26, x_6, x_5, x_27, x_1, x_9, x_10, x_11, x_12, x_24);
lean_dec(x_9);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_17);
if (x_29 == 0)
{
return x_17;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_17, 0);
x_31 = lean_ctor_get(x_17, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_17);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addSimpTheorem___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addSimpTheorem___lam__0(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addSimpTheorem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = lean_unbox(x_6);
lean_dec(x_6);
x_16 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addSimpTheorem(x_1, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs_isSimproc_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
lean_inc(x_4);
x_5 = l_Lean_Meta_Simp_isSimproc___redArg(x_4, x_2, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = lean_box(0);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_5, 0);
lean_dec(x_15);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_5, 0, x_16);
return x_5;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_dec(x_5);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_4);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_3);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs_isSimproc_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_elabSimpArgs_isSimproc_x3f___redArg(x_1, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs_isSimproc_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_elabSimpArgs_isSimproc_x3f___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs_isSimproc_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_elabSimpArgs_isSimproc_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Meta_getSimpExtension_x3f(x_1, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = l_Lean_Meta_Simp_getSimprocExtension_x3f(x_1, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
if (lean_obj_tag(x_13) == 0)
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_22; 
lean_dec(x_18);
x_22 = lean_box(0);
lean_ctor_set(x_11, 1, x_17);
lean_ctor_set(x_11, 0, x_22);
return x_11;
}
else
{
lean_free_object(x_11);
goto block_21;
}
}
else
{
lean_free_object(x_11);
goto block_21;
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_16);
if (lean_is_scalar(x_18)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_18;
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_25 = l_Lean_Meta_Simp_getSimprocExtension_x3f(x_1, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_28 = x_25;
} else {
 lean_dec_ref(x_25);
 x_28 = lean_box(0);
}
if (lean_obj_tag(x_23) == 0)
{
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_28);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_27);
return x_33;
}
else
{
goto block_31;
}
}
else
{
goto block_31;
}
block_31:
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_26);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_mk_string_unchecked("ident", 5, 5);
x_12 = l_Lean_Name_mkStr1(x_11);
lean_inc(x_1);
x_13 = l_Lean_Syntax_isOfKind(x_1, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Term_elabCDotFunctionAlias_x3f(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_box(0);
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
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_14, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_15, 0);
lean_inc(x_25);
lean_dec(x_15);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_14, 0, x_26);
return x_14;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_dec(x_14);
x_28 = lean_ctor_get(x_15, 0);
lean_inc(x_28);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_29 = x_15;
} else {
 lean_dec_ref(x_15);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(1, 1, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
return x_31;
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_14);
if (x_32 == 0)
{
return x_14;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_14, 0);
x_34 = lean_ctor_get(x_14, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_14);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_50; lean_object* x_51; lean_object* x_55; lean_object* x_56; 
x_36 = l_Lean_Elab_Tactic_saveState___redArg(x_3, x_5, x_7, x_8, x_9, x_10);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_55 = lean_mk_string_unchecked("term", 4, 4);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_56 = l_Lean_Elab_Term_resolveId_x3f(x_1, x_55, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_38);
lean_dec(x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
lean_dec(x_39);
lean_dec(x_37);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_60 = lean_erase_macro_scopes(x_59);
x_61 = l_Lean_Meta_Simp_isBuiltinSimproc(x_60, x_8, x_9, x_58);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_unbox(x_62);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___lam__0(x_60, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_64);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_65;
}
else
{
uint8_t x_66; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_66 = !lean_is_exclusive(x_61);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_61, 0);
lean_dec(x_67);
x_68 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_68, 0, x_60);
lean_ctor_set(x_61, 0, x_68);
return x_61;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_61, 1);
lean_inc(x_69);
lean_dec(x_61);
x_70 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_70, 0, x_60);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
}
else
{
lean_object* x_72; uint8_t x_73; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_72 = lean_ctor_get(x_56, 1);
lean_inc(x_72);
lean_dec(x_56);
x_73 = !lean_is_exclusive(x_57);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_57, 0);
lean_inc(x_74);
x_75 = l_Lean_Elab_Tactic_elabSimpArgs_isSimproc_x3f___redArg(x_74, x_9, x_72);
lean_dec(x_9);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
if (lean_obj_tag(x_76) == 0)
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_75);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_75, 0);
lean_dec(x_78);
lean_ctor_set(x_75, 0, x_57);
return x_75;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_75, 1);
lean_inc(x_79);
lean_dec(x_75);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_57);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
else
{
uint8_t x_81; 
lean_free_object(x_57);
lean_dec(x_74);
x_81 = !lean_is_exclusive(x_75);
if (x_81 == 0)
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_ctor_get(x_75, 0);
lean_dec(x_82);
x_83 = !lean_is_exclusive(x_76);
if (x_83 == 0)
{
lean_ctor_set_tag(x_76, 2);
return x_75;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_76, 0);
lean_inc(x_84);
lean_dec(x_76);
x_85 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_75, 0, x_85);
return x_75;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_75, 1);
lean_inc(x_86);
lean_dec(x_75);
x_87 = lean_ctor_get(x_76, 0);
lean_inc(x_87);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_88 = x_76;
} else {
 lean_dec_ref(x_76);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(2, 1, 0);
} else {
 x_89 = x_88;
 lean_ctor_set_tag(x_89, 2);
}
lean_ctor_set(x_89, 0, x_87);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_86);
return x_90;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_57, 0);
lean_inc(x_91);
lean_dec(x_57);
lean_inc(x_91);
x_92 = l_Lean_Elab_Tactic_elabSimpArgs_isSimproc_x3f___redArg(x_91, x_9, x_72);
lean_dec(x_9);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_95 = x_92;
} else {
 lean_dec_ref(x_92);
 x_95 = lean_box(0);
}
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_91);
if (lean_is_scalar(x_95)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_95;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_94);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_91);
x_98 = lean_ctor_get(x_92, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_99 = x_92;
} else {
 lean_dec_ref(x_92);
 x_99 = lean_box(0);
}
x_100 = lean_ctor_get(x_93, 0);
lean_inc(x_100);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 x_101 = x_93;
} else {
 lean_dec_ref(x_93);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(2, 1, 0);
} else {
 x_102 = x_101;
 lean_ctor_set_tag(x_102, 2);
}
lean_ctor_set(x_102, 0, x_100);
if (lean_is_scalar(x_99)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_99;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_98);
return x_103;
}
}
}
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_56, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_56, 1);
lean_inc(x_105);
lean_dec(x_56);
x_50 = x_104;
x_51 = x_105;
goto block_54;
}
block_49:
{
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_41);
lean_dec(x_39);
x_43 = l_Lean_Elab_Tactic_SavedState_restore(x_37, x_42, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_40);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_46 = lean_erase_macro_scopes(x_45);
x_47 = l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___lam__0(x_46, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_44);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_47;
}
else
{
lean_object* x_48; 
lean_dec(x_37);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_39)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_39;
 lean_ctor_set_tag(x_48, 1);
}
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set(x_48, 1, x_40);
return x_48;
}
}
block_54:
{
uint8_t x_52; 
x_52 = l_Lean_Exception_isInterrupt(x_50);
if (x_52 == 0)
{
uint8_t x_53; 
x_53 = l_Lean_Exception_isRuntime(x_50);
x_40 = x_51;
x_41 = x_50;
x_42 = x_53;
goto block_49;
}
else
{
x_40 = x_51;
x_41 = x_50;
x_42 = x_52;
goto block_49;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_3, x_2);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_23; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_16 = lean_unsigned_to_nat(1u);
x_28 = lean_array_uget(x_1, x_3);
lean_inc(x_28);
x_29 = l_Lean_Syntax_getKind(x_28);
x_30 = lean_mk_string_unchecked("Lean", 4, 4);
x_31 = lean_mk_string_unchecked("Parser", 6, 6);
x_32 = lean_mk_string_unchecked("Tactic", 6, 6);
x_33 = lean_mk_string_unchecked("simpLemma", 9, 9);
x_34 = l_Lean_Name_mkStr4(x_30, x_31, x_32, x_33);
x_35 = lean_name_eq(x_29, x_34);
lean_dec(x_34);
lean_dec(x_29);
if (x_35 == 0)
{
lean_dec(x_28);
x_17 = x_4;
x_18 = x_13;
goto block_22;
}
else
{
uint8_t x_36; lean_object* x_209; lean_object* x_210; uint8_t x_211; 
x_209 = lean_unsigned_to_nat(0u);
x_210 = l_Lean_Syntax_getArg(x_28, x_209);
x_211 = l_Lean_Syntax_isNone(x_210);
lean_dec(x_210);
if (x_211 == 0)
{
x_36 = x_211;
goto block_208;
}
else
{
lean_object* x_212; uint8_t x_213; 
x_212 = l_Lean_Syntax_getArg(x_28, x_16);
x_213 = l_Lean_Syntax_isNone(x_212);
lean_dec(x_212);
x_36 = x_213;
goto block_208;
}
block_208:
{
if (x_36 == 0)
{
lean_dec(x_28);
x_17 = x_4;
x_18 = x_13;
goto block_22;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_unsigned_to_nat(2u);
x_38 = l_Lean_Syntax_getArg(x_28, x_37);
lean_dec(x_28);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_39 = l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f(x_38, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
switch (lean_obj_tag(x_40)) {
case 1:
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
switch (lean_obj_tag(x_42)) {
case 0:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Expr_bvar___override(x_44);
lean_ctor_set(x_40, 0, x_45);
x_46 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet_spec__0___lam__0(x_4, x_40, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_43);
lean_dec(x_40);
x_23 = x_46;
goto block_27;
}
case 1:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_free_object(x_40);
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
lean_dec(x_39);
x_48 = lean_ctor_get(x_42, 0);
lean_inc(x_48);
lean_dec(x_42);
lean_inc(x_9);
lean_inc(x_48);
x_49 = l_Lean_FVarId_getDecl___redArg(x_48, x_9, x_11, x_12, x_47);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lean_LocalDecl_isLet(x_50);
lean_dec(x_50);
if (x_52 == 0)
{
lean_dec(x_48);
x_17 = x_4;
x_18 = x_51;
goto block_22;
}
else
{
lean_object* x_53; 
x_53 = l_Lean_FVarIdSet_insert(x_4, x_48);
x_17 = x_53;
x_18 = x_51;
goto block_22;
}
}
else
{
uint8_t x_54; 
lean_dec(x_48);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_54 = !lean_is_exclusive(x_49);
if (x_54 == 0)
{
return x_49;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_49, 0);
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_49);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
case 2:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_39, 1);
lean_inc(x_58);
lean_dec(x_39);
x_59 = lean_ctor_get(x_42, 0);
lean_inc(x_59);
lean_dec(x_42);
x_60 = l_Lean_Expr_mvar___override(x_59);
lean_ctor_set(x_40, 0, x_60);
x_61 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet_spec__0___lam__0(x_4, x_40, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_58);
lean_dec(x_40);
x_23 = x_61;
goto block_27;
}
case 3:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_39, 1);
lean_inc(x_62);
lean_dec(x_39);
x_63 = lean_ctor_get(x_42, 0);
lean_inc(x_63);
lean_dec(x_42);
x_64 = l_Lean_Expr_sort___override(x_63);
lean_ctor_set(x_40, 0, x_64);
x_65 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet_spec__0___lam__0(x_4, x_40, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_62);
lean_dec(x_40);
x_23 = x_65;
goto block_27;
}
case 4:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_39, 1);
lean_inc(x_66);
lean_dec(x_39);
x_67 = lean_ctor_get(x_42, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_42, 1);
lean_inc(x_68);
lean_dec(x_42);
x_69 = l_Lean_Expr_const___override(x_67, x_68);
lean_ctor_set(x_40, 0, x_69);
x_70 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet_spec__0___lam__0(x_4, x_40, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_66);
lean_dec(x_40);
x_23 = x_70;
goto block_27;
}
case 5:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_39, 1);
lean_inc(x_71);
lean_dec(x_39);
x_72 = lean_ctor_get(x_42, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_42, 1);
lean_inc(x_73);
lean_dec(x_42);
x_74 = l_Lean_Expr_app___override(x_72, x_73);
lean_ctor_set(x_40, 0, x_74);
x_75 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet_spec__0___lam__0(x_4, x_40, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_71);
lean_dec(x_40);
x_23 = x_75;
goto block_27;
}
case 6:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; 
x_76 = lean_ctor_get(x_39, 1);
lean_inc(x_76);
lean_dec(x_39);
x_77 = lean_ctor_get(x_42, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_42, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_42, 2);
lean_inc(x_79);
x_80 = lean_ctor_get_uint8(x_42, sizeof(void*)*3 + 8);
lean_dec(x_42);
x_81 = l_Lean_Expr_lam___override(x_77, x_78, x_79, x_80);
lean_ctor_set(x_40, 0, x_81);
x_82 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet_spec__0___lam__0(x_4, x_40, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_76);
lean_dec(x_40);
x_23 = x_82;
goto block_27;
}
case 7:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; 
x_83 = lean_ctor_get(x_39, 1);
lean_inc(x_83);
lean_dec(x_39);
x_84 = lean_ctor_get(x_42, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_42, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_42, 2);
lean_inc(x_86);
x_87 = lean_ctor_get_uint8(x_42, sizeof(void*)*3 + 8);
lean_dec(x_42);
x_88 = l_Lean_Expr_forallE___override(x_84, x_85, x_86, x_87);
lean_ctor_set(x_40, 0, x_88);
x_89 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet_spec__0___lam__0(x_4, x_40, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_83);
lean_dec(x_40);
x_23 = x_89;
goto block_27;
}
case 8:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; 
x_90 = lean_ctor_get(x_39, 1);
lean_inc(x_90);
lean_dec(x_39);
x_91 = lean_ctor_get(x_42, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_42, 1);
lean_inc(x_92);
x_93 = lean_ctor_get(x_42, 2);
lean_inc(x_93);
x_94 = lean_ctor_get(x_42, 3);
lean_inc(x_94);
x_95 = lean_ctor_get_uint8(x_42, sizeof(void*)*4 + 8);
lean_dec(x_42);
x_96 = l_Lean_Expr_letE___override(x_91, x_92, x_93, x_94, x_95);
lean_ctor_set(x_40, 0, x_96);
x_97 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet_spec__0___lam__0(x_4, x_40, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_90);
lean_dec(x_40);
x_23 = x_97;
goto block_27;
}
case 9:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_39, 1);
lean_inc(x_98);
lean_dec(x_39);
x_99 = lean_ctor_get(x_42, 0);
lean_inc(x_99);
lean_dec(x_42);
x_100 = l_Lean_Expr_lit___override(x_99);
lean_ctor_set(x_40, 0, x_100);
x_101 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet_spec__0___lam__0(x_4, x_40, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_98);
lean_dec(x_40);
x_23 = x_101;
goto block_27;
}
case 10:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_102 = lean_ctor_get(x_39, 1);
lean_inc(x_102);
lean_dec(x_39);
x_103 = lean_ctor_get(x_42, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_42, 1);
lean_inc(x_104);
lean_dec(x_42);
x_105 = l_Lean_Expr_mdata___override(x_103, x_104);
lean_ctor_set(x_40, 0, x_105);
x_106 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet_spec__0___lam__0(x_4, x_40, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_102);
lean_dec(x_40);
x_23 = x_106;
goto block_27;
}
default: 
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_107 = lean_ctor_get(x_39, 1);
lean_inc(x_107);
lean_dec(x_39);
x_108 = lean_ctor_get(x_42, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_42, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_42, 2);
lean_inc(x_110);
lean_dec(x_42);
x_111 = l_Lean_Expr_proj___override(x_108, x_109, x_110);
lean_ctor_set(x_40, 0, x_111);
x_112 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet_spec__0___lam__0(x_4, x_40, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_107);
lean_dec(x_40);
x_23 = x_112;
goto block_27;
}
}
}
else
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_40, 0);
lean_inc(x_113);
lean_dec(x_40);
switch (lean_obj_tag(x_113)) {
case 0:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_114 = lean_ctor_get(x_39, 1);
lean_inc(x_114);
lean_dec(x_39);
x_115 = lean_ctor_get(x_113, 0);
lean_inc(x_115);
lean_dec(x_113);
x_116 = l_Lean_Expr_bvar___override(x_115);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_118 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet_spec__0___lam__0(x_4, x_117, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_114);
lean_dec(x_117);
x_23 = x_118;
goto block_27;
}
case 1:
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_39, 1);
lean_inc(x_119);
lean_dec(x_39);
x_120 = lean_ctor_get(x_113, 0);
lean_inc(x_120);
lean_dec(x_113);
lean_inc(x_9);
lean_inc(x_120);
x_121 = l_Lean_FVarId_getDecl___redArg(x_120, x_9, x_11, x_12, x_119);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = l_Lean_LocalDecl_isLet(x_122);
lean_dec(x_122);
if (x_124 == 0)
{
lean_dec(x_120);
x_17 = x_4;
x_18 = x_123;
goto block_22;
}
else
{
lean_object* x_125; 
x_125 = l_Lean_FVarIdSet_insert(x_4, x_120);
x_17 = x_125;
x_18 = x_123;
goto block_22;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_120);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_126 = lean_ctor_get(x_121, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_121, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_128 = x_121;
} else {
 lean_dec_ref(x_121);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
}
case 2:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_130 = lean_ctor_get(x_39, 1);
lean_inc(x_130);
lean_dec(x_39);
x_131 = lean_ctor_get(x_113, 0);
lean_inc(x_131);
lean_dec(x_113);
x_132 = l_Lean_Expr_mvar___override(x_131);
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_132);
x_134 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet_spec__0___lam__0(x_4, x_133, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_130);
lean_dec(x_133);
x_23 = x_134;
goto block_27;
}
case 3:
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_135 = lean_ctor_get(x_39, 1);
lean_inc(x_135);
lean_dec(x_39);
x_136 = lean_ctor_get(x_113, 0);
lean_inc(x_136);
lean_dec(x_113);
x_137 = l_Lean_Expr_sort___override(x_136);
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_137);
x_139 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet_spec__0___lam__0(x_4, x_138, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_135);
lean_dec(x_138);
x_23 = x_139;
goto block_27;
}
case 4:
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_140 = lean_ctor_get(x_39, 1);
lean_inc(x_140);
lean_dec(x_39);
x_141 = lean_ctor_get(x_113, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_113, 1);
lean_inc(x_142);
lean_dec(x_113);
x_143 = l_Lean_Expr_const___override(x_141, x_142);
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_143);
x_145 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet_spec__0___lam__0(x_4, x_144, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_140);
lean_dec(x_144);
x_23 = x_145;
goto block_27;
}
case 5:
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_146 = lean_ctor_get(x_39, 1);
lean_inc(x_146);
lean_dec(x_39);
x_147 = lean_ctor_get(x_113, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_113, 1);
lean_inc(x_148);
lean_dec(x_113);
x_149 = l_Lean_Expr_app___override(x_147, x_148);
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_149);
x_151 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet_spec__0___lam__0(x_4, x_150, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_146);
lean_dec(x_150);
x_23 = x_151;
goto block_27;
}
case 6:
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_152 = lean_ctor_get(x_39, 1);
lean_inc(x_152);
lean_dec(x_39);
x_153 = lean_ctor_get(x_113, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_113, 1);
lean_inc(x_154);
x_155 = lean_ctor_get(x_113, 2);
lean_inc(x_155);
x_156 = lean_ctor_get_uint8(x_113, sizeof(void*)*3 + 8);
lean_dec(x_113);
x_157 = l_Lean_Expr_lam___override(x_153, x_154, x_155, x_156);
x_158 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_158, 0, x_157);
x_159 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet_spec__0___lam__0(x_4, x_158, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_152);
lean_dec(x_158);
x_23 = x_159;
goto block_27;
}
case 7:
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_160 = lean_ctor_get(x_39, 1);
lean_inc(x_160);
lean_dec(x_39);
x_161 = lean_ctor_get(x_113, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_113, 1);
lean_inc(x_162);
x_163 = lean_ctor_get(x_113, 2);
lean_inc(x_163);
x_164 = lean_ctor_get_uint8(x_113, sizeof(void*)*3 + 8);
lean_dec(x_113);
x_165 = l_Lean_Expr_forallE___override(x_161, x_162, x_163, x_164);
x_166 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_166, 0, x_165);
x_167 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet_spec__0___lam__0(x_4, x_166, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_160);
lean_dec(x_166);
x_23 = x_167;
goto block_27;
}
case 8:
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_168 = lean_ctor_get(x_39, 1);
lean_inc(x_168);
lean_dec(x_39);
x_169 = lean_ctor_get(x_113, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_113, 1);
lean_inc(x_170);
x_171 = lean_ctor_get(x_113, 2);
lean_inc(x_171);
x_172 = lean_ctor_get(x_113, 3);
lean_inc(x_172);
x_173 = lean_ctor_get_uint8(x_113, sizeof(void*)*4 + 8);
lean_dec(x_113);
x_174 = l_Lean_Expr_letE___override(x_169, x_170, x_171, x_172, x_173);
x_175 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_175, 0, x_174);
x_176 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet_spec__0___lam__0(x_4, x_175, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_168);
lean_dec(x_175);
x_23 = x_176;
goto block_27;
}
case 9:
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_177 = lean_ctor_get(x_39, 1);
lean_inc(x_177);
lean_dec(x_39);
x_178 = lean_ctor_get(x_113, 0);
lean_inc(x_178);
lean_dec(x_113);
x_179 = l_Lean_Expr_lit___override(x_178);
x_180 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_180, 0, x_179);
x_181 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet_spec__0___lam__0(x_4, x_180, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_177);
lean_dec(x_180);
x_23 = x_181;
goto block_27;
}
case 10:
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_182 = lean_ctor_get(x_39, 1);
lean_inc(x_182);
lean_dec(x_39);
x_183 = lean_ctor_get(x_113, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_113, 1);
lean_inc(x_184);
lean_dec(x_113);
x_185 = l_Lean_Expr_mdata___override(x_183, x_184);
x_186 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_186, 0, x_185);
x_187 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet_spec__0___lam__0(x_4, x_186, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_182);
lean_dec(x_186);
x_23 = x_187;
goto block_27;
}
default: 
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_188 = lean_ctor_get(x_39, 1);
lean_inc(x_188);
lean_dec(x_39);
x_189 = lean_ctor_get(x_113, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_113, 1);
lean_inc(x_190);
x_191 = lean_ctor_get(x_113, 2);
lean_inc(x_191);
lean_dec(x_113);
x_192 = l_Lean_Expr_proj___override(x_189, x_190, x_191);
x_193 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_193, 0, x_192);
x_194 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet_spec__0___lam__0(x_4, x_193, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_188);
lean_dec(x_193);
x_23 = x_194;
goto block_27;
}
}
}
}
case 3:
{
lean_object* x_195; uint8_t x_196; 
x_195 = lean_ctor_get(x_39, 1);
lean_inc(x_195);
lean_dec(x_39);
x_196 = !lean_is_exclusive(x_40);
if (x_196 == 0)
{
lean_object* x_197; 
x_197 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet_spec__0___lam__0(x_4, x_40, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_195);
lean_dec(x_40);
x_23 = x_197;
goto block_27;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_198 = lean_ctor_get(x_40, 0);
x_199 = lean_ctor_get(x_40, 1);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_40);
x_200 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
x_201 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet_spec__0___lam__0(x_4, x_200, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_195);
lean_dec(x_200);
x_23 = x_201;
goto block_27;
}
}
default: 
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_39, 1);
lean_inc(x_202);
lean_dec(x_39);
x_203 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet_spec__0___lam__0(x_4, x_40, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_202);
lean_dec(x_40);
x_23 = x_203;
goto block_27;
}
}
}
else
{
uint8_t x_204; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_204 = !lean_is_exclusive(x_39);
if (x_204 == 0)
{
return x_39;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_39, 0);
x_206 = lean_ctor_get(x_39, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_39);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
}
}
}
}
block_22:
{
size_t x_19; size_t x_20; 
x_19 = lean_usize_of_nat(x_16);
x_20 = lean_usize_add(x_3, x_19);
x_3 = x_20;
x_4 = x_17;
x_13 = x_18;
goto _start;
}
block_27:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_17 = x_26;
x_18 = x_25;
goto block_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get_uint8(x_12, sizeof(void*)*2 + 16);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; size_t x_36; lean_object* x_37; size_t x_38; lean_object* x_39; 
x_14 = lean_box(0);
x_15 = lean_unsigned_to_nat(1u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = l_Lean_Syntax_getSepArgs(x_16);
lean_dec(x_16);
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_5, 1);
x_20 = lean_ctor_get_uint8(x_5, sizeof(void*)*7);
x_21 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 1);
x_22 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 2);
x_23 = lean_ctor_get(x_5, 2);
x_24 = lean_ctor_get(x_5, 3);
x_25 = lean_ctor_get(x_5, 4);
x_26 = lean_ctor_get(x_5, 5);
x_27 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 3);
x_28 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 4);
x_29 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 5);
x_30 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 6);
x_31 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 7);
x_32 = lean_ctor_get(x_5, 6);
x_33 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 8);
x_34 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 9);
lean_inc(x_32);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_19);
lean_inc(x_18);
x_35 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_35, 0, x_18);
lean_ctor_set(x_35, 1, x_19);
lean_ctor_set(x_35, 2, x_23);
lean_ctor_set(x_35, 3, x_24);
lean_ctor_set(x_35, 4, x_25);
lean_ctor_set(x_35, 5, x_26);
lean_ctor_set(x_35, 6, x_32);
lean_ctor_set_uint8(x_35, sizeof(void*)*7, x_20);
lean_ctor_set_uint8(x_35, sizeof(void*)*7 + 1, x_21);
lean_ctor_set_uint8(x_35, sizeof(void*)*7 + 2, x_22);
lean_ctor_set_uint8(x_35, sizeof(void*)*7 + 3, x_27);
lean_ctor_set_uint8(x_35, sizeof(void*)*7 + 4, x_28);
lean_ctor_set_uint8(x_35, sizeof(void*)*7 + 5, x_29);
lean_ctor_set_uint8(x_35, sizeof(void*)*7 + 6, x_30);
lean_ctor_set_uint8(x_35, sizeof(void*)*7 + 7, x_31);
lean_ctor_set_uint8(x_35, sizeof(void*)*7 + 8, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*7 + 9, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*7 + 10, x_13);
x_36 = lean_array_size(x_17);
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_usize_of_nat(x_37);
x_39 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet_spec__0(x_17, x_36, x_38, x_14, x_3, x_4, x_35, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_17);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_11);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet_spec__0(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___Lean_Meta_SimpTheorems_erase___at___Lean_Elab_Tactic_elabSimpArgs_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 2);
lean_inc(x_11);
x_12 = l_Lean_warningAsError;
x_13 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_box(1);
x_15 = lean_unbox(x_14);
x_16 = l_Lean_log___at___Lean_logError___at___Lean_Elab_logException___at___Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__2_spec__2(x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_box(2);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_log___at___Lean_logError___at___Lean_Elab_logException___at___Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__2_spec__2(x_1, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at___Lean_Elab_Tactic_elabSimpArgs_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_27; 
x_13 = lean_mk_string_unchecked("'", 1, 1);
x_14 = l_Lean_stringToMessageData(x_13);
lean_dec(x_13);
x_27 = lean_ctor_get(x_2, 0);
lean_inc(x_27);
lean_dec(x_2);
x_15 = x_27;
goto block_26;
block_26:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_16 = l_Lean_MessageData_ofName(x_15);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_mk_string_unchecked("' does not have [simp] attribute", 32, 32);
x_19 = l_Lean_stringToMessageData(x_18);
lean_dec(x_18);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_logWarning___at___Lean_Meta_SimpTheorems_erase___at___Lean_Elab_Tactic_elabSimpArgs_spec__0_spec__0(x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_1);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at___Lean_Elab_Tactic_elabSimpArgs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_25; 
lean_inc(x_1);
x_25 = l_Lean_Meta_SimpTheorems_isLemma(x_1, x_2);
if (x_25 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
lean_inc(x_1);
x_27 = l_Lean_Meta_SimpTheorems_isDeclToUnfold(x_1, x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_1, 5);
lean_inc(x_28);
x_29 = l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0(lean_box(0), x_28, x_26);
lean_dec(x_26);
x_12 = x_29;
goto block_24;
}
else
{
lean_dec(x_26);
x_12 = x_27;
goto block_24;
}
}
else
{
x_12 = x_25;
goto block_24;
}
}
else
{
x_12 = x_25;
goto block_24;
}
block_24:
{
if (x_12 == 0)
{
lean_object* x_13; 
lean_inc(x_2);
x_13 = l_Lean_Meta_Origin_converse(x_2);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l_Lean_Meta_SimpTheorems_erase___at___Lean_Elab_Tactic_elabSimpArgs_spec__0___lam__0(x_1, x_2, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
lean_inc(x_1);
x_17 = l_Lean_Meta_SimpTheorems_isLemma(x_1, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = l_Lean_Meta_SimpTheorems_erase___at___Lean_Elab_Tactic_elabSimpArgs_spec__0___lam__0(x_1, x_2, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_9);
lean_dec(x_2);
x_20 = l_Lean_Meta_SimpTheorems_eraseCore(x_1, x_16);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_11);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_9);
x_22 = l_Lean_Meta_SimpTheorems_eraseCore(x_1, x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_11);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_Elab_Tactic_elabSimpArgs_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_mkUnknownIdentifierMessage(x_1);
x_8 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_Elab_Tactic_elabSimpArgs_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_Elab_Tactic_elabSimpArgs_spec__2_spec__2___redArg(x_2, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_Elab_Tactic_elabSimpArgs_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_mk_string_unchecked("unknown constant '", 18, 18);
x_12 = l_Lean_stringToMessageData(x_11);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
x_15 = l_Lean_MessageData_ofConstName(x_1, x_14);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_mk_string_unchecked("'", 1, 1);
x_18 = l_Lean_stringToMessageData(x_17);
lean_dec(x_17);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_Elab_Tactic_elabSimpArgs_spec__2_spec__2___redArg(x_19, x_6, x_7, x_8, x_9, x_10);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_Elab_Tactic_elabSimpArgs_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwUnknownConstant___at___Lean_Elab_Tactic_elabSimpArgs_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_Elab_Tactic_elabSimpArgs_spec__4___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_st_ref_take(x_1, x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_nat_add(x_13, x_7);
lean_inc(x_12);
lean_ctor_set(x_8, 1, x_14);
lean_ctor_set(x_8, 0, x_12);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_10, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_10, 4);
lean_inc(x_18);
x_19 = lean_ctor_get(x_10, 5);
lean_inc(x_19);
x_20 = lean_ctor_get(x_10, 6);
lean_inc(x_20);
x_21 = lean_ctor_get(x_10, 7);
lean_inc(x_21);
lean_dec(x_10);
x_22 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_16);
lean_ctor_set(x_22, 2, x_8);
lean_ctor_set(x_22, 3, x_17);
lean_ctor_set(x_22, 4, x_18);
lean_ctor_set(x_22, 5, x_19);
lean_ctor_set(x_22, 6, x_20);
lean_ctor_set(x_22, 7, x_21);
x_23 = lean_st_ref_set(x_1, x_22, x_11);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = l_Lean_Name_num___override(x_12, x_13);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = l_Lean_Name_num___override(x_12, x_13);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_30 = lean_ctor_get(x_8, 0);
x_31 = lean_ctor_get(x_8, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_8);
x_32 = lean_ctor_get(x_6, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_6, 1);
lean_inc(x_33);
lean_dec(x_6);
x_34 = lean_nat_add(x_33, x_7);
lean_inc(x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_30, 3);
lean_inc(x_38);
x_39 = lean_ctor_get(x_30, 4);
lean_inc(x_39);
x_40 = lean_ctor_get(x_30, 5);
lean_inc(x_40);
x_41 = lean_ctor_get(x_30, 6);
lean_inc(x_41);
x_42 = lean_ctor_get(x_30, 7);
lean_inc(x_42);
lean_dec(x_30);
x_43 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_43, 0, x_36);
lean_ctor_set(x_43, 1, x_37);
lean_ctor_set(x_43, 2, x_35);
lean_ctor_set(x_43, 3, x_38);
lean_ctor_set(x_43, 4, x_39);
lean_ctor_set(x_43, 5, x_40);
lean_ctor_set(x_43, 6, x_41);
lean_ctor_set(x_43, 7, x_42);
x_44 = lean_st_ref_set(x_1, x_43, x_31);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
x_47 = l_Lean_Name_num___override(x_32, x_33);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_Elab_Tactic_elabSimpArgs_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_mkFreshId___at___Lean_Elab_Tactic_elabSimpArgs_spec__4___redArg(x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_spec__5_spec__5___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = l_Lean_Elab_Tactic_saveState___redArg(x_12, x_14, x_16, x_17, x_18, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_23 = x_20;
} else {
 lean_dec_ref(x_20);
 x_23 = lean_box(0);
}
x_24 = l_Lean_Syntax_getArg(x_1, x_2);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_24);
x_25 = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(x_24, x_10, x_17, x_18, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_21);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_26);
x_28 = l_Lean_Meta_Simp_isSimproc___redArg(x_26, x_18, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_3, 0);
x_32 = lean_ctor_get_uint8(x_31, sizeof(void*)*2 + 11);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_dec(x_28);
x_34 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_4);
lean_ctor_set_uint8(x_34, sizeof(void*)*1 + 1, x_5);
x_35 = lean_ctor_get(x_17, 5);
lean_inc(x_35);
x_36 = l_Lean_replaceRef(x_24, x_35);
lean_dec(x_35);
lean_dec(x_24);
x_37 = lean_ctor_get(x_17, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_17, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_17, 2);
lean_inc(x_39);
x_40 = lean_ctor_get(x_17, 3);
lean_inc(x_40);
x_41 = lean_ctor_get(x_17, 4);
lean_inc(x_41);
x_42 = lean_ctor_get(x_17, 6);
lean_inc(x_42);
x_43 = lean_ctor_get(x_17, 7);
lean_inc(x_43);
x_44 = lean_ctor_get(x_17, 8);
lean_inc(x_44);
x_45 = lean_ctor_get(x_17, 9);
lean_inc(x_45);
x_46 = lean_ctor_get(x_17, 10);
lean_inc(x_46);
x_47 = lean_ctor_get_uint8(x_17, sizeof(void*)*13);
x_48 = lean_ctor_get(x_17, 11);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_17, sizeof(void*)*13 + 1);
x_50 = lean_ctor_get(x_17, 12);
lean_inc(x_50);
lean_dec(x_17);
x_51 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_51, 0, x_37);
lean_ctor_set(x_51, 1, x_38);
lean_ctor_set(x_51, 2, x_39);
lean_ctor_set(x_51, 3, x_40);
lean_ctor_set(x_51, 4, x_41);
lean_ctor_set(x_51, 5, x_36);
lean_ctor_set(x_51, 6, x_42);
lean_ctor_set(x_51, 7, x_43);
lean_ctor_set(x_51, 8, x_44);
lean_ctor_set(x_51, 9, x_45);
lean_ctor_set(x_51, 10, x_46);
lean_ctor_set(x_51, 11, x_48);
lean_ctor_set(x_51, 12, x_50);
lean_ctor_set_uint8(x_51, sizeof(void*)*13, x_47);
lean_ctor_set_uint8(x_51, sizeof(void*)*13 + 1, x_49);
x_52 = l_Lean_Meta_SimpTheorems_erase___at___Lean_Elab_Tactic_elabSimpArgs_spec__0(x_9, x_34, x_11, x_12, x_13, x_14, x_15, x_16, x_51, x_18, x_33);
lean_dec(x_18);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_box(0);
if (lean_is_scalar(x_23)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_23;
}
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_6);
x_57 = lean_box(x_7);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_8);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_52, 0, x_60);
return x_52;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_61 = lean_ctor_get(x_52, 0);
x_62 = lean_ctor_get(x_52, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_52);
x_63 = lean_box(0);
if (lean_is_scalar(x_23)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_23;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_6);
x_65 = lean_box(x_7);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_8);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_63);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_62);
return x_69;
}
}
else
{
uint8_t x_70; 
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_17);
x_70 = !lean_is_exclusive(x_28);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_71 = lean_ctor_get(x_28, 0);
lean_dec(x_71);
x_72 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_72, 0, x_26);
lean_ctor_set_uint8(x_72, sizeof(void*)*1, x_4);
lean_ctor_set_uint8(x_72, sizeof(void*)*1 + 1, x_5);
x_73 = l_Lean_Meta_SimpTheorems_eraseCore(x_9, x_72);
x_74 = lean_box(0);
if (lean_is_scalar(x_23)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_23;
}
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_6);
x_76 = lean_box(x_7);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_8);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_74);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_28, 0, x_79);
return x_28;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_80 = lean_ctor_get(x_28, 1);
lean_inc(x_80);
lean_dec(x_28);
x_81 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_81, 0, x_26);
lean_ctor_set_uint8(x_81, sizeof(void*)*1, x_4);
lean_ctor_set_uint8(x_81, sizeof(void*)*1 + 1, x_5);
x_82 = l_Lean_Meta_SimpTheorems_eraseCore(x_9, x_81);
x_83 = lean_box(0);
if (lean_is_scalar(x_23)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_23;
}
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_6);
x_85 = lean_box(x_7);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_8);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_83);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_80);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_17);
x_90 = !lean_is_exclusive(x_28);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_91 = lean_ctor_get(x_28, 0);
lean_dec(x_91);
x_92 = l_Lean_Meta_Simp_SimprocsArray_erase(x_8, x_26);
x_93 = lean_box(0);
if (lean_is_scalar(x_23)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_23;
}
lean_ctor_set(x_94, 0, x_9);
lean_ctor_set(x_94, 1, x_6);
x_95 = lean_box(x_7);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_92);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_93);
lean_ctor_set(x_98, 1, x_97);
lean_ctor_set(x_28, 0, x_98);
return x_28;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_99 = lean_ctor_get(x_28, 1);
lean_inc(x_99);
lean_dec(x_28);
x_100 = l_Lean_Meta_Simp_SimprocsArray_erase(x_8, x_26);
x_101 = lean_box(0);
if (lean_is_scalar(x_23)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_23;
}
lean_ctor_set(x_102, 0, x_9);
lean_ctor_set(x_102, 1, x_6);
x_103 = lean_box(x_7);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_102);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_100);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_101);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_99);
return x_107;
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_201; 
x_108 = lean_ctor_get(x_25, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_25, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_110 = x_25;
} else {
 lean_dec_ref(x_25);
 x_110 = lean_box(0);
}
x_201 = l_Lean_Exception_isInterrupt(x_108);
if (x_201 == 0)
{
uint8_t x_202; 
x_202 = l_Lean_Exception_isRuntime(x_108);
x_111 = x_202;
goto block_200;
}
else
{
x_111 = x_201;
goto block_200;
}
block_200:
{
if (x_111 == 0)
{
lean_object* x_112; uint8_t x_113; 
lean_dec(x_110);
lean_dec(x_108);
x_112 = l_Lean_Elab_Tactic_SavedState_restore(x_21, x_111, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_109);
x_113 = !lean_is_exclusive(x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_114 = lean_ctor_get(x_112, 1);
x_115 = lean_ctor_get(x_112, 0);
lean_dec(x_115);
x_116 = l_Lean_Syntax_getId(x_24);
x_117 = lean_erase_macro_scopes(x_116);
x_118 = l_Lean_Meta_Simp_isBuiltinSimproc(x_117, x_17, x_18, x_114);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_unbox(x_119);
lean_dec(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
lean_free_object(x_112);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
lean_dec(x_118);
x_122 = lean_ctor_get(x_17, 5);
lean_inc(x_122);
x_123 = l_Lean_replaceRef(x_24, x_122);
lean_dec(x_122);
lean_dec(x_24);
x_124 = lean_ctor_get(x_17, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_17, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_17, 2);
lean_inc(x_126);
x_127 = lean_ctor_get(x_17, 3);
lean_inc(x_127);
x_128 = lean_ctor_get(x_17, 4);
lean_inc(x_128);
x_129 = lean_ctor_get(x_17, 6);
lean_inc(x_129);
x_130 = lean_ctor_get(x_17, 7);
lean_inc(x_130);
x_131 = lean_ctor_get(x_17, 8);
lean_inc(x_131);
x_132 = lean_ctor_get(x_17, 9);
lean_inc(x_132);
x_133 = lean_ctor_get(x_17, 10);
lean_inc(x_133);
x_134 = lean_ctor_get_uint8(x_17, sizeof(void*)*13);
x_135 = lean_ctor_get(x_17, 11);
lean_inc(x_135);
x_136 = lean_ctor_get_uint8(x_17, sizeof(void*)*13 + 1);
x_137 = lean_ctor_get(x_17, 12);
lean_inc(x_137);
lean_dec(x_17);
x_138 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_138, 0, x_124);
lean_ctor_set(x_138, 1, x_125);
lean_ctor_set(x_138, 2, x_126);
lean_ctor_set(x_138, 3, x_127);
lean_ctor_set(x_138, 4, x_128);
lean_ctor_set(x_138, 5, x_123);
lean_ctor_set(x_138, 6, x_129);
lean_ctor_set(x_138, 7, x_130);
lean_ctor_set(x_138, 8, x_131);
lean_ctor_set(x_138, 9, x_132);
lean_ctor_set(x_138, 10, x_133);
lean_ctor_set(x_138, 11, x_135);
lean_ctor_set(x_138, 12, x_137);
lean_ctor_set_uint8(x_138, sizeof(void*)*13, x_134);
lean_ctor_set_uint8(x_138, sizeof(void*)*13 + 1, x_136);
x_139 = l_Lean_throwUnknownConstant___at___Lean_Elab_Tactic_elabSimpArgs_spec__2___redArg(x_117, x_11, x_12, x_13, x_14, x_15, x_16, x_138, x_18, x_121);
lean_dec(x_18);
lean_dec(x_138);
x_140 = !lean_is_exclusive(x_139);
if (x_140 == 0)
{
return x_139;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_139, 0);
x_142 = lean_ctor_get(x_139, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_139);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
else
{
uint8_t x_144; 
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_17);
x_144 = !lean_is_exclusive(x_118);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_145 = lean_ctor_get(x_118, 0);
lean_dec(x_145);
x_146 = l_Lean_Meta_Simp_SimprocsArray_erase(x_8, x_117);
x_147 = lean_box(0);
lean_ctor_set(x_112, 1, x_6);
lean_ctor_set(x_112, 0, x_9);
x_148 = lean_box(x_7);
if (lean_is_scalar(x_23)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_23;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_112);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_146);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_147);
lean_ctor_set(x_151, 1, x_150);
lean_ctor_set(x_118, 0, x_151);
return x_118;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_152 = lean_ctor_get(x_118, 1);
lean_inc(x_152);
lean_dec(x_118);
x_153 = l_Lean_Meta_Simp_SimprocsArray_erase(x_8, x_117);
x_154 = lean_box(0);
lean_ctor_set(x_112, 1, x_6);
lean_ctor_set(x_112, 0, x_9);
x_155 = lean_box(x_7);
if (lean_is_scalar(x_23)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_23;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_112);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_153);
lean_ctor_set(x_157, 1, x_156);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_154);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_152);
return x_159;
}
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_160 = lean_ctor_get(x_112, 1);
lean_inc(x_160);
lean_dec(x_112);
x_161 = l_Lean_Syntax_getId(x_24);
x_162 = lean_erase_macro_scopes(x_161);
x_163 = l_Lean_Meta_Simp_isBuiltinSimproc(x_162, x_17, x_18, x_160);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_unbox(x_164);
lean_dec(x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; uint8_t x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_166 = lean_ctor_get(x_163, 1);
lean_inc(x_166);
lean_dec(x_163);
x_167 = lean_ctor_get(x_17, 5);
lean_inc(x_167);
x_168 = l_Lean_replaceRef(x_24, x_167);
lean_dec(x_167);
lean_dec(x_24);
x_169 = lean_ctor_get(x_17, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_17, 1);
lean_inc(x_170);
x_171 = lean_ctor_get(x_17, 2);
lean_inc(x_171);
x_172 = lean_ctor_get(x_17, 3);
lean_inc(x_172);
x_173 = lean_ctor_get(x_17, 4);
lean_inc(x_173);
x_174 = lean_ctor_get(x_17, 6);
lean_inc(x_174);
x_175 = lean_ctor_get(x_17, 7);
lean_inc(x_175);
x_176 = lean_ctor_get(x_17, 8);
lean_inc(x_176);
x_177 = lean_ctor_get(x_17, 9);
lean_inc(x_177);
x_178 = lean_ctor_get(x_17, 10);
lean_inc(x_178);
x_179 = lean_ctor_get_uint8(x_17, sizeof(void*)*13);
x_180 = lean_ctor_get(x_17, 11);
lean_inc(x_180);
x_181 = lean_ctor_get_uint8(x_17, sizeof(void*)*13 + 1);
x_182 = lean_ctor_get(x_17, 12);
lean_inc(x_182);
lean_dec(x_17);
x_183 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_183, 0, x_169);
lean_ctor_set(x_183, 1, x_170);
lean_ctor_set(x_183, 2, x_171);
lean_ctor_set(x_183, 3, x_172);
lean_ctor_set(x_183, 4, x_173);
lean_ctor_set(x_183, 5, x_168);
lean_ctor_set(x_183, 6, x_174);
lean_ctor_set(x_183, 7, x_175);
lean_ctor_set(x_183, 8, x_176);
lean_ctor_set(x_183, 9, x_177);
lean_ctor_set(x_183, 10, x_178);
lean_ctor_set(x_183, 11, x_180);
lean_ctor_set(x_183, 12, x_182);
lean_ctor_set_uint8(x_183, sizeof(void*)*13, x_179);
lean_ctor_set_uint8(x_183, sizeof(void*)*13 + 1, x_181);
x_184 = l_Lean_throwUnknownConstant___at___Lean_Elab_Tactic_elabSimpArgs_spec__2___redArg(x_162, x_11, x_12, x_13, x_14, x_15, x_16, x_183, x_18, x_166);
lean_dec(x_18);
lean_dec(x_183);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_187 = x_184;
} else {
 lean_dec_ref(x_184);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_186);
return x_188;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_17);
x_189 = lean_ctor_get(x_163, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_190 = x_163;
} else {
 lean_dec_ref(x_163);
 x_190 = lean_box(0);
}
x_191 = l_Lean_Meta_Simp_SimprocsArray_erase(x_8, x_162);
x_192 = lean_box(0);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_9);
lean_ctor_set(x_193, 1, x_6);
x_194 = lean_box(x_7);
if (lean_is_scalar(x_23)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_23;
}
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_193);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_191);
lean_ctor_set(x_196, 1, x_195);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_192);
lean_ctor_set(x_197, 1, x_196);
if (lean_is_scalar(x_190)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_190;
}
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_189);
return x_198;
}
}
}
else
{
lean_object* x_199; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
if (lean_is_scalar(x_110)) {
 x_199 = lean_alloc_ctor(1, 2, 0);
} else {
 x_199 = x_110;
}
lean_ctor_set(x_199, 0, x_108);
lean_ctor_set(x_199, 1, x_109);
return x_199;
}
}
}
}
else
{
uint8_t x_203; 
lean_dec(x_18);
lean_dec(x_17);
x_203 = !lean_is_exclusive(x_10);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_204 = lean_ctor_get(x_10, 0);
x_205 = l_Lean_Expr_fvarId_x21(x_204);
lean_dec(x_204);
lean_ctor_set(x_10, 0, x_205);
x_206 = l_Lean_Meta_SimpTheorems_eraseCore(x_9, x_10);
x_207 = lean_box(0);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_6);
x_209 = lean_box(x_7);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_208);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_8);
lean_ctor_set(x_211, 1, x_210);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_207);
lean_ctor_set(x_212, 1, x_211);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_19);
return x_213;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_214 = lean_ctor_get(x_10, 0);
lean_inc(x_214);
lean_dec(x_10);
x_215 = l_Lean_Expr_fvarId_x21(x_214);
lean_dec(x_214);
x_216 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_216, 0, x_215);
x_217 = l_Lean_Meta_SimpTheorems_eraseCore(x_9, x_216);
x_218 = lean_box(0);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_6);
x_220 = lean_box(x_7);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_219);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_8);
lean_ctor_set(x_222, 1, x_221);
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_218);
lean_ctor_set(x_223, 1, x_222);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_19);
return x_224;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_spec__5_spec__5(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_7, x_6);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_70; lean_object* x_378; lean_object* x_379; uint8_t x_380; uint8_t x_381; lean_object* x_385; lean_object* x_386; lean_object* x_392; lean_object* x_393; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; uint8_t x_405; lean_object* x_466; lean_object* x_467; uint8_t x_468; 
x_20 = lean_unsigned_to_nat(1u);
x_28 = l_Lean_Syntax_isNone(x_2);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_array_uget(x_5, x_7);
x_31 = lean_ctor_get(x_8, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_8, 1);
lean_inc(x_32);
lean_dec(x_8);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_30);
x_401 = l_Lean_Syntax_getKind(x_30);
x_402 = lean_mk_string_unchecked("Lean", 4, 4);
x_403 = lean_mk_string_unchecked("Parser", 6, 6);
x_404 = lean_mk_string_unchecked("Tactic", 6, 6);
x_466 = lean_mk_string_unchecked("simpErase", 9, 9);
lean_inc(x_404);
lean_inc(x_403);
lean_inc(x_402);
x_467 = l_Lean_Name_mkStr4(x_402, x_403, x_404, x_466);
x_468 = lean_name_eq(x_401, x_467);
lean_dec(x_467);
if (x_468 == 0)
{
x_405 = x_468;
goto block_465;
}
else
{
x_405 = x_18;
goto block_465;
}
block_27:
{
lean_object* x_23; size_t x_24; size_t x_25; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_usize_of_nat(x_20);
x_25 = lean_usize_add(x_7, x_24);
x_7 = x_25;
x_8 = x_23;
x_17 = x_22;
goto _start;
}
block_60:
{
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = l_Lean_Elab_Tactic_SavedState_restore(x_39, x_40, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_37);
x_42 = lean_ctor_get_uint8(x_9, sizeof(void*)*1);
if (x_42 == 0)
{
uint8_t x_43; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_43 = !lean_is_exclusive(x_41);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_41, 0);
lean_dec(x_44);
lean_ctor_set_tag(x_41, 1);
lean_ctor_set(x_41, 0, x_38);
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_dec(x_41);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_38);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_41, 1);
lean_inc(x_47);
lean_dec(x_41);
lean_inc(x_15);
x_48 = l_Lean_Elab_logException___at___Lean_Elab_Tactic_closeUsingOrAdmit_spec__0(x_38, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_35);
lean_ctor_set(x_51, 1, x_36);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_33);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_31);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_49);
lean_ctor_set(x_54, 1, x_53);
x_21 = x_54;
x_22 = x_50;
goto block_27;
}
else
{
uint8_t x_55; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_55 = !lean_is_exclusive(x_48);
if (x_55 == 0)
{
return x_48;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_48, 0);
x_57 = lean_ctor_get(x_48, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_48);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
else
{
lean_object* x_59; 
lean_dec(x_39);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_38);
lean_ctor_set(x_59, 1, x_37);
return x_59;
}
}
block_66:
{
uint8_t x_64; 
x_64 = l_Lean_Exception_isInterrupt(x_62);
if (x_64 == 0)
{
uint8_t x_65; 
x_65 = l_Lean_Exception_isRuntime(x_62);
x_37 = x_63;
x_38 = x_62;
x_39 = x_61;
x_40 = x_65;
goto block_60;
}
else
{
x_37 = x_63;
x_38 = x_62;
x_39 = x_61;
x_40 = x_64;
goto block_60;
}
}
block_377:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_unsigned_to_nat(2u);
x_72 = l_Lean_Syntax_getArg(x_30, x_71);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_72);
x_73 = l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f(x_72, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_67);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
switch (lean_obj_tag(x_74)) {
case 0:
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_73);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_76 = lean_ctor_get(x_73, 1);
x_77 = lean_ctor_get(x_73, 0);
lean_dec(x_77);
x_78 = l_Lean_mkFreshId___at___Lean_Elab_Tactic_elabSimpArgs_spec__4___redArg(x_16, x_76);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_78, 1);
x_81 = lean_ctor_get(x_1, 4);
lean_ctor_set_tag(x_78, 2);
lean_ctor_set(x_78, 1, x_30);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_35);
x_82 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addSimpTheorem(x_81, x_35, x_78, x_72, x_69, x_70, x_11, x_12, x_13, x_14, x_15, x_16, x_80);
if (lean_obj_tag(x_82) == 0)
{
uint8_t x_83; 
lean_dec(x_68);
lean_dec(x_35);
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_82, 1);
x_85 = lean_box(0);
lean_ctor_set(x_82, 1, x_36);
lean_ctor_set(x_73, 1, x_82);
lean_ctor_set(x_73, 0, x_33);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_31);
lean_ctor_set(x_86, 1, x_73);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_21 = x_87;
x_22 = x_84;
goto block_27;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_88 = lean_ctor_get(x_82, 0);
x_89 = lean_ctor_get(x_82, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_82);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_36);
lean_ctor_set(x_73, 1, x_91);
lean_ctor_set(x_73, 0, x_33);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_31);
lean_ctor_set(x_92, 1, x_73);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_92);
x_21 = x_93;
x_22 = x_89;
goto block_27;
}
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_free_object(x_73);
x_94 = lean_ctor_get(x_82, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_82, 1);
lean_inc(x_95);
lean_dec(x_82);
x_61 = x_68;
x_62 = x_94;
x_63 = x_95;
goto block_66;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_ctor_get(x_78, 0);
x_97 = lean_ctor_get(x_78, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_78);
x_98 = lean_ctor_get(x_1, 4);
x_99 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_30);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_35);
x_100 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addSimpTheorem(x_98, x_35, x_99, x_72, x_69, x_70, x_11, x_12, x_13, x_14, x_15, x_16, x_97);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_68);
lean_dec(x_35);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_103 = x_100;
} else {
 lean_dec_ref(x_100);
 x_103 = lean_box(0);
}
x_104 = lean_box(0);
if (lean_is_scalar(x_103)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_103;
}
lean_ctor_set(x_105, 0, x_101);
lean_ctor_set(x_105, 1, x_36);
lean_ctor_set(x_73, 1, x_105);
lean_ctor_set(x_73, 0, x_33);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_31);
lean_ctor_set(x_106, 1, x_73);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_106);
x_21 = x_107;
x_22 = x_102;
goto block_27;
}
else
{
lean_object* x_108; lean_object* x_109; 
lean_free_object(x_73);
x_108 = lean_ctor_get(x_100, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_100, 1);
lean_inc(x_109);
lean_dec(x_100);
x_61 = x_68;
x_62 = x_108;
x_63 = x_109;
goto block_66;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_110 = lean_ctor_get(x_73, 1);
lean_inc(x_110);
lean_dec(x_73);
x_111 = l_Lean_mkFreshId___at___Lean_Elab_Tactic_elabSimpArgs_spec__4___redArg(x_16, x_110);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_114 = x_111;
} else {
 lean_dec_ref(x_111);
 x_114 = lean_box(0);
}
x_115 = lean_ctor_get(x_1, 4);
if (lean_is_scalar(x_114)) {
 x_116 = lean_alloc_ctor(2, 2, 0);
} else {
 x_116 = x_114;
 lean_ctor_set_tag(x_116, 2);
}
lean_ctor_set(x_116, 0, x_112);
lean_ctor_set(x_116, 1, x_30);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_35);
x_117 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addSimpTheorem(x_115, x_35, x_116, x_72, x_69, x_70, x_11, x_12, x_13, x_14, x_15, x_16, x_113);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_68);
lean_dec(x_35);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_120 = x_117;
} else {
 lean_dec_ref(x_117);
 x_120 = lean_box(0);
}
x_121 = lean_box(0);
if (lean_is_scalar(x_120)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_120;
}
lean_ctor_set(x_122, 0, x_118);
lean_ctor_set(x_122, 1, x_36);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_33);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_31);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_121);
lean_ctor_set(x_125, 1, x_124);
x_21 = x_125;
x_22 = x_119;
goto block_27;
}
else
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_117, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_117, 1);
lean_inc(x_127);
lean_dec(x_117);
x_61 = x_68;
x_62 = x_126;
x_63 = x_127;
goto block_66;
}
}
}
case 1:
{
uint8_t x_128; 
lean_dec(x_72);
x_128 = !lean_is_exclusive(x_73);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_129 = lean_ctor_get(x_73, 1);
x_130 = lean_ctor_get(x_73, 0);
lean_dec(x_130);
x_131 = lean_ctor_get(x_74, 0);
lean_inc(x_131);
lean_dec(x_74);
x_132 = l_Lean_mkFreshId___at___Lean_Elab_Tactic_elabSimpArgs_spec__4___redArg(x_16, x_129);
x_133 = !lean_is_exclusive(x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_132, 1);
x_135 = lean_ctor_get(x_1, 4);
lean_ctor_set_tag(x_132, 2);
lean_ctor_set(x_132, 1, x_30);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_35);
x_136 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem(x_135, x_35, x_132, x_131, x_69, x_70, x_3, x_13, x_14, x_15, x_16, x_134);
if (lean_obj_tag(x_136) == 0)
{
uint8_t x_137; 
lean_dec(x_68);
lean_dec(x_35);
x_137 = !lean_is_exclusive(x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_138 = lean_ctor_get(x_136, 1);
x_139 = lean_box(0);
lean_ctor_set(x_136, 1, x_36);
lean_ctor_set(x_73, 1, x_136);
lean_ctor_set(x_73, 0, x_33);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_31);
lean_ctor_set(x_140, 1, x_73);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
x_21 = x_141;
x_22 = x_138;
goto block_27;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_142 = lean_ctor_get(x_136, 0);
x_143 = lean_ctor_get(x_136, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_136);
x_144 = lean_box(0);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_36);
lean_ctor_set(x_73, 1, x_145);
lean_ctor_set(x_73, 0, x_33);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_31);
lean_ctor_set(x_146, 1, x_73);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_146);
x_21 = x_147;
x_22 = x_143;
goto block_27;
}
}
else
{
lean_object* x_148; lean_object* x_149; 
lean_free_object(x_73);
x_148 = lean_ctor_get(x_136, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_136, 1);
lean_inc(x_149);
lean_dec(x_136);
x_61 = x_68;
x_62 = x_148;
x_63 = x_149;
goto block_66;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_150 = lean_ctor_get(x_132, 0);
x_151 = lean_ctor_get(x_132, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_132);
x_152 = lean_ctor_get(x_1, 4);
x_153 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_30);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_35);
x_154 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem(x_152, x_35, x_153, x_131, x_69, x_70, x_3, x_13, x_14, x_15, x_16, x_151);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_68);
lean_dec(x_35);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_157 = x_154;
} else {
 lean_dec_ref(x_154);
 x_157 = lean_box(0);
}
x_158 = lean_box(0);
if (lean_is_scalar(x_157)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_157;
}
lean_ctor_set(x_159, 0, x_155);
lean_ctor_set(x_159, 1, x_36);
lean_ctor_set(x_73, 1, x_159);
lean_ctor_set(x_73, 0, x_33);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_31);
lean_ctor_set(x_160, 1, x_73);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_160);
x_21 = x_161;
x_22 = x_156;
goto block_27;
}
else
{
lean_object* x_162; lean_object* x_163; 
lean_free_object(x_73);
x_162 = lean_ctor_get(x_154, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_154, 1);
lean_inc(x_163);
lean_dec(x_154);
x_61 = x_68;
x_62 = x_162;
x_63 = x_163;
goto block_66;
}
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_164 = lean_ctor_get(x_73, 1);
lean_inc(x_164);
lean_dec(x_73);
x_165 = lean_ctor_get(x_74, 0);
lean_inc(x_165);
lean_dec(x_74);
x_166 = l_Lean_mkFreshId___at___Lean_Elab_Tactic_elabSimpArgs_spec__4___redArg(x_16, x_164);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_169 = x_166;
} else {
 lean_dec_ref(x_166);
 x_169 = lean_box(0);
}
x_170 = lean_ctor_get(x_1, 4);
if (lean_is_scalar(x_169)) {
 x_171 = lean_alloc_ctor(2, 2, 0);
} else {
 x_171 = x_169;
 lean_ctor_set_tag(x_171, 2);
}
lean_ctor_set(x_171, 0, x_167);
lean_ctor_set(x_171, 1, x_30);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_35);
x_172 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem(x_170, x_35, x_171, x_165, x_69, x_70, x_3, x_13, x_14, x_15, x_16, x_168);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_68);
lean_dec(x_35);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_175 = x_172;
} else {
 lean_dec_ref(x_172);
 x_175 = lean_box(0);
}
x_176 = lean_box(0);
if (lean_is_scalar(x_175)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_175;
}
lean_ctor_set(x_177, 0, x_173);
lean_ctor_set(x_177, 1, x_36);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_33);
lean_ctor_set(x_178, 1, x_177);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_31);
lean_ctor_set(x_179, 1, x_178);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_176);
lean_ctor_set(x_180, 1, x_179);
x_21 = x_180;
x_22 = x_174;
goto block_27;
}
else
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_172, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_172, 1);
lean_inc(x_182);
lean_dec(x_172);
x_61 = x_68;
x_62 = x_181;
x_63 = x_182;
goto block_66;
}
}
}
case 2:
{
uint8_t x_183; 
lean_dec(x_72);
lean_dec(x_30);
x_183 = !lean_is_exclusive(x_73);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_184 = lean_ctor_get(x_73, 1);
x_185 = lean_ctor_get(x_73, 0);
lean_dec(x_185);
x_186 = lean_ctor_get(x_74, 0);
lean_inc(x_186);
lean_dec(x_74);
lean_inc(x_31);
x_187 = l_Lean_Meta_Simp_SimprocsArray_add(x_31, x_186, x_69, x_15, x_16, x_184);
if (lean_obj_tag(x_187) == 0)
{
uint8_t x_188; 
lean_dec(x_68);
lean_dec(x_31);
x_188 = !lean_is_exclusive(x_187);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_189 = lean_ctor_get(x_187, 0);
x_190 = lean_ctor_get(x_187, 1);
x_191 = lean_box(0);
lean_ctor_set(x_187, 1, x_36);
lean_ctor_set(x_187, 0, x_35);
lean_ctor_set(x_73, 1, x_187);
lean_ctor_set(x_73, 0, x_33);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_189);
lean_ctor_set(x_192, 1, x_73);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
x_21 = x_193;
x_22 = x_190;
goto block_27;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_194 = lean_ctor_get(x_187, 0);
x_195 = lean_ctor_get(x_187, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_187);
x_196 = lean_box(0);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_35);
lean_ctor_set(x_197, 1, x_36);
lean_ctor_set(x_73, 1, x_197);
lean_ctor_set(x_73, 0, x_33);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_194);
lean_ctor_set(x_198, 1, x_73);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_196);
lean_ctor_set(x_199, 1, x_198);
x_21 = x_199;
x_22 = x_195;
goto block_27;
}
}
else
{
lean_object* x_200; lean_object* x_201; 
lean_free_object(x_73);
x_200 = lean_ctor_get(x_187, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_187, 1);
lean_inc(x_201);
lean_dec(x_187);
x_61 = x_68;
x_62 = x_200;
x_63 = x_201;
goto block_66;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_73, 1);
lean_inc(x_202);
lean_dec(x_73);
x_203 = lean_ctor_get(x_74, 0);
lean_inc(x_203);
lean_dec(x_74);
lean_inc(x_31);
x_204 = l_Lean_Meta_Simp_SimprocsArray_add(x_31, x_203, x_69, x_15, x_16, x_202);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_68);
lean_dec(x_31);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_207 = x_204;
} else {
 lean_dec_ref(x_204);
 x_207 = lean_box(0);
}
x_208 = lean_box(0);
if (lean_is_scalar(x_207)) {
 x_209 = lean_alloc_ctor(0, 2, 0);
} else {
 x_209 = x_207;
}
lean_ctor_set(x_209, 0, x_35);
lean_ctor_set(x_209, 1, x_36);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_33);
lean_ctor_set(x_210, 1, x_209);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_205);
lean_ctor_set(x_211, 1, x_210);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_208);
lean_ctor_set(x_212, 1, x_211);
x_21 = x_212;
x_22 = x_206;
goto block_27;
}
else
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_ctor_get(x_204, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_204, 1);
lean_inc(x_214);
lean_dec(x_204);
x_61 = x_68;
x_62 = x_213;
x_63 = x_214;
goto block_66;
}
}
}
default: 
{
lean_object* x_215; 
lean_dec(x_72);
lean_dec(x_68);
lean_dec(x_30);
x_215 = lean_ctor_get(x_74, 0);
lean_inc(x_215);
if (lean_obj_tag(x_215) == 0)
{
uint8_t x_216; 
x_216 = !lean_is_exclusive(x_74);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; uint8_t x_219; 
x_217 = lean_ctor_get(x_74, 1);
x_218 = lean_ctor_get(x_74, 0);
lean_dec(x_218);
x_219 = !lean_is_exclusive(x_73);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_220 = lean_ctor_get(x_73, 1);
x_221 = lean_ctor_get(x_73, 0);
lean_dec(x_221);
x_222 = lean_ctor_get(x_217, 0);
lean_inc(x_222);
lean_dec(x_217);
x_223 = l_Lean_Meta_Simp_SimprocExtension_getSimprocs___redArg(x_222, x_16, x_220);
lean_dec(x_222);
x_224 = !lean_is_exclusive(x_223);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_225 = lean_ctor_get(x_223, 0);
x_226 = lean_ctor_get(x_223, 1);
x_227 = lean_array_push(x_31, x_225);
x_228 = lean_box(0);
lean_ctor_set(x_223, 1, x_36);
lean_ctor_set(x_223, 0, x_35);
lean_ctor_set_tag(x_74, 0);
lean_ctor_set(x_74, 1, x_223);
lean_ctor_set(x_74, 0, x_33);
lean_ctor_set(x_73, 1, x_74);
lean_ctor_set(x_73, 0, x_227);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_73);
x_21 = x_229;
x_22 = x_226;
goto block_27;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_230 = lean_ctor_get(x_223, 0);
x_231 = lean_ctor_get(x_223, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_223);
x_232 = lean_array_push(x_31, x_230);
x_233 = lean_box(0);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_35);
lean_ctor_set(x_234, 1, x_36);
lean_ctor_set_tag(x_74, 0);
lean_ctor_set(x_74, 1, x_234);
lean_ctor_set(x_74, 0, x_33);
lean_ctor_set(x_73, 1, x_74);
lean_ctor_set(x_73, 0, x_232);
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_73);
x_21 = x_235;
x_22 = x_231;
goto block_27;
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_236 = lean_ctor_get(x_73, 1);
lean_inc(x_236);
lean_dec(x_73);
x_237 = lean_ctor_get(x_217, 0);
lean_inc(x_237);
lean_dec(x_217);
x_238 = l_Lean_Meta_Simp_SimprocExtension_getSimprocs___redArg(x_237, x_16, x_236);
lean_dec(x_237);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_241 = x_238;
} else {
 lean_dec_ref(x_238);
 x_241 = lean_box(0);
}
x_242 = lean_array_push(x_31, x_239);
x_243 = lean_box(0);
if (lean_is_scalar(x_241)) {
 x_244 = lean_alloc_ctor(0, 2, 0);
} else {
 x_244 = x_241;
}
lean_ctor_set(x_244, 0, x_35);
lean_ctor_set(x_244, 1, x_36);
lean_ctor_set_tag(x_74, 0);
lean_ctor_set(x_74, 1, x_244);
lean_ctor_set(x_74, 0, x_33);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_242);
lean_ctor_set(x_245, 1, x_74);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_243);
lean_ctor_set(x_246, 1, x_245);
x_21 = x_246;
x_22 = x_240;
goto block_27;
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_247 = lean_ctor_get(x_74, 1);
lean_inc(x_247);
lean_dec(x_74);
x_248 = lean_ctor_get(x_73, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_249 = x_73;
} else {
 lean_dec_ref(x_73);
 x_249 = lean_box(0);
}
x_250 = lean_ctor_get(x_247, 0);
lean_inc(x_250);
lean_dec(x_247);
x_251 = l_Lean_Meta_Simp_SimprocExtension_getSimprocs___redArg(x_250, x_16, x_248);
lean_dec(x_250);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 x_254 = x_251;
} else {
 lean_dec_ref(x_251);
 x_254 = lean_box(0);
}
x_255 = lean_array_push(x_31, x_252);
x_256 = lean_box(0);
if (lean_is_scalar(x_254)) {
 x_257 = lean_alloc_ctor(0, 2, 0);
} else {
 x_257 = x_254;
}
lean_ctor_set(x_257, 0, x_35);
lean_ctor_set(x_257, 1, x_36);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_33);
lean_ctor_set(x_258, 1, x_257);
if (lean_is_scalar(x_249)) {
 x_259 = lean_alloc_ctor(0, 2, 0);
} else {
 x_259 = x_249;
}
lean_ctor_set(x_259, 0, x_255);
lean_ctor_set(x_259, 1, x_258);
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_256);
lean_ctor_set(x_260, 1, x_259);
x_21 = x_260;
x_22 = x_253;
goto block_27;
}
}
else
{
uint8_t x_261; 
x_261 = !lean_is_exclusive(x_74);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; 
x_262 = lean_ctor_get(x_74, 1);
x_263 = lean_ctor_get(x_74, 0);
lean_dec(x_263);
if (lean_obj_tag(x_262) == 0)
{
uint8_t x_264; 
x_264 = !lean_is_exclusive(x_73);
if (x_264 == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; 
x_265 = lean_ctor_get(x_73, 1);
x_266 = lean_ctor_get(x_73, 0);
lean_dec(x_266);
x_267 = lean_ctor_get(x_215, 0);
lean_inc(x_267);
lean_dec(x_215);
x_268 = l_Lean_Meta_SimpExtension_getTheorems___redArg(x_267, x_16, x_265);
lean_dec(x_267);
x_269 = !lean_is_exclusive(x_268);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_270 = lean_ctor_get(x_268, 0);
x_271 = lean_ctor_get(x_268, 1);
x_272 = lean_array_push(x_36, x_270);
x_273 = lean_box(0);
lean_ctor_set(x_268, 1, x_272);
lean_ctor_set(x_268, 0, x_35);
lean_ctor_set_tag(x_74, 0);
lean_ctor_set(x_74, 1, x_268);
lean_ctor_set(x_74, 0, x_33);
lean_ctor_set(x_73, 1, x_74);
lean_ctor_set(x_73, 0, x_31);
x_274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_73);
x_21 = x_274;
x_22 = x_271;
goto block_27;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_275 = lean_ctor_get(x_268, 0);
x_276 = lean_ctor_get(x_268, 1);
lean_inc(x_276);
lean_inc(x_275);
lean_dec(x_268);
x_277 = lean_array_push(x_36, x_275);
x_278 = lean_box(0);
x_279 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_279, 0, x_35);
lean_ctor_set(x_279, 1, x_277);
lean_ctor_set_tag(x_74, 0);
lean_ctor_set(x_74, 1, x_279);
lean_ctor_set(x_74, 0, x_33);
lean_ctor_set(x_73, 1, x_74);
lean_ctor_set(x_73, 0, x_31);
x_280 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_73);
x_21 = x_280;
x_22 = x_276;
goto block_27;
}
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_281 = lean_ctor_get(x_73, 1);
lean_inc(x_281);
lean_dec(x_73);
x_282 = lean_ctor_get(x_215, 0);
lean_inc(x_282);
lean_dec(x_215);
x_283 = l_Lean_Meta_SimpExtension_getTheorems___redArg(x_282, x_16, x_281);
lean_dec(x_282);
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_283, 1);
lean_inc(x_285);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 x_286 = x_283;
} else {
 lean_dec_ref(x_283);
 x_286 = lean_box(0);
}
x_287 = lean_array_push(x_36, x_284);
x_288 = lean_box(0);
if (lean_is_scalar(x_286)) {
 x_289 = lean_alloc_ctor(0, 2, 0);
} else {
 x_289 = x_286;
}
lean_ctor_set(x_289, 0, x_35);
lean_ctor_set(x_289, 1, x_287);
lean_ctor_set_tag(x_74, 0);
lean_ctor_set(x_74, 1, x_289);
lean_ctor_set(x_74, 0, x_33);
x_290 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_290, 0, x_31);
lean_ctor_set(x_290, 1, x_74);
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_288);
lean_ctor_set(x_291, 1, x_290);
x_21 = x_291;
x_22 = x_285;
goto block_27;
}
}
else
{
uint8_t x_292; 
x_292 = !lean_is_exclusive(x_73);
if (x_292 == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; uint8_t x_298; 
x_293 = lean_ctor_get(x_73, 1);
x_294 = lean_ctor_get(x_73, 0);
lean_dec(x_294);
x_295 = lean_ctor_get(x_215, 0);
lean_inc(x_295);
lean_dec(x_215);
x_296 = lean_ctor_get(x_262, 0);
lean_inc(x_296);
lean_dec(x_262);
x_297 = l_Lean_Meta_SimpExtension_getTheorems___redArg(x_295, x_16, x_293);
lean_dec(x_295);
x_298 = !lean_is_exclusive(x_297);
if (x_298 == 0)
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; 
x_299 = lean_ctor_get(x_297, 0);
x_300 = lean_ctor_get(x_297, 1);
x_301 = l_Lean_Meta_Simp_SimprocExtension_getSimprocs___redArg(x_296, x_16, x_300);
lean_dec(x_296);
x_302 = !lean_is_exclusive(x_301);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_303 = lean_ctor_get(x_301, 0);
x_304 = lean_ctor_get(x_301, 1);
x_305 = lean_array_push(x_36, x_299);
x_306 = lean_array_push(x_31, x_303);
x_307 = lean_box(0);
lean_ctor_set(x_301, 1, x_305);
lean_ctor_set(x_301, 0, x_35);
lean_ctor_set(x_297, 1, x_301);
lean_ctor_set(x_297, 0, x_33);
lean_ctor_set_tag(x_74, 0);
lean_ctor_set(x_74, 1, x_297);
lean_ctor_set(x_74, 0, x_306);
lean_ctor_set(x_73, 1, x_74);
lean_ctor_set(x_73, 0, x_307);
x_21 = x_73;
x_22 = x_304;
goto block_27;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_308 = lean_ctor_get(x_301, 0);
x_309 = lean_ctor_get(x_301, 1);
lean_inc(x_309);
lean_inc(x_308);
lean_dec(x_301);
x_310 = lean_array_push(x_36, x_299);
x_311 = lean_array_push(x_31, x_308);
x_312 = lean_box(0);
x_313 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_313, 0, x_35);
lean_ctor_set(x_313, 1, x_310);
lean_ctor_set(x_297, 1, x_313);
lean_ctor_set(x_297, 0, x_33);
lean_ctor_set_tag(x_74, 0);
lean_ctor_set(x_74, 1, x_297);
lean_ctor_set(x_74, 0, x_311);
lean_ctor_set(x_73, 1, x_74);
lean_ctor_set(x_73, 0, x_312);
x_21 = x_73;
x_22 = x_309;
goto block_27;
}
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_314 = lean_ctor_get(x_297, 0);
x_315 = lean_ctor_get(x_297, 1);
lean_inc(x_315);
lean_inc(x_314);
lean_dec(x_297);
x_316 = l_Lean_Meta_Simp_SimprocExtension_getSimprocs___redArg(x_296, x_16, x_315);
lean_dec(x_296);
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_316, 1);
lean_inc(x_318);
if (lean_is_exclusive(x_316)) {
 lean_ctor_release(x_316, 0);
 lean_ctor_release(x_316, 1);
 x_319 = x_316;
} else {
 lean_dec_ref(x_316);
 x_319 = lean_box(0);
}
x_320 = lean_array_push(x_36, x_314);
x_321 = lean_array_push(x_31, x_317);
x_322 = lean_box(0);
if (lean_is_scalar(x_319)) {
 x_323 = lean_alloc_ctor(0, 2, 0);
} else {
 x_323 = x_319;
}
lean_ctor_set(x_323, 0, x_35);
lean_ctor_set(x_323, 1, x_320);
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_33);
lean_ctor_set(x_324, 1, x_323);
lean_ctor_set_tag(x_74, 0);
lean_ctor_set(x_74, 1, x_324);
lean_ctor_set(x_74, 0, x_321);
lean_ctor_set(x_73, 1, x_74);
lean_ctor_set(x_73, 0, x_322);
x_21 = x_73;
x_22 = x_318;
goto block_27;
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_325 = lean_ctor_get(x_73, 1);
lean_inc(x_325);
lean_dec(x_73);
x_326 = lean_ctor_get(x_215, 0);
lean_inc(x_326);
lean_dec(x_215);
x_327 = lean_ctor_get(x_262, 0);
lean_inc(x_327);
lean_dec(x_262);
x_328 = l_Lean_Meta_SimpExtension_getTheorems___redArg(x_326, x_16, x_325);
lean_dec(x_326);
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_328, 1);
lean_inc(x_330);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 lean_ctor_release(x_328, 1);
 x_331 = x_328;
} else {
 lean_dec_ref(x_328);
 x_331 = lean_box(0);
}
x_332 = l_Lean_Meta_Simp_SimprocExtension_getSimprocs___redArg(x_327, x_16, x_330);
lean_dec(x_327);
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_332, 1);
lean_inc(x_334);
if (lean_is_exclusive(x_332)) {
 lean_ctor_release(x_332, 0);
 lean_ctor_release(x_332, 1);
 x_335 = x_332;
} else {
 lean_dec_ref(x_332);
 x_335 = lean_box(0);
}
x_336 = lean_array_push(x_36, x_329);
x_337 = lean_array_push(x_31, x_333);
x_338 = lean_box(0);
if (lean_is_scalar(x_335)) {
 x_339 = lean_alloc_ctor(0, 2, 0);
} else {
 x_339 = x_335;
}
lean_ctor_set(x_339, 0, x_35);
lean_ctor_set(x_339, 1, x_336);
if (lean_is_scalar(x_331)) {
 x_340 = lean_alloc_ctor(0, 2, 0);
} else {
 x_340 = x_331;
}
lean_ctor_set(x_340, 0, x_33);
lean_ctor_set(x_340, 1, x_339);
lean_ctor_set_tag(x_74, 0);
lean_ctor_set(x_74, 1, x_340);
lean_ctor_set(x_74, 0, x_337);
x_341 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_341, 0, x_338);
lean_ctor_set(x_341, 1, x_74);
x_21 = x_341;
x_22 = x_334;
goto block_27;
}
}
}
else
{
lean_object* x_342; 
x_342 = lean_ctor_get(x_74, 1);
lean_inc(x_342);
lean_dec(x_74);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_343 = lean_ctor_get(x_73, 1);
lean_inc(x_343);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_344 = x_73;
} else {
 lean_dec_ref(x_73);
 x_344 = lean_box(0);
}
x_345 = lean_ctor_get(x_215, 0);
lean_inc(x_345);
lean_dec(x_215);
x_346 = l_Lean_Meta_SimpExtension_getTheorems___redArg(x_345, x_16, x_343);
lean_dec(x_345);
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_346, 1);
lean_inc(x_348);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 lean_ctor_release(x_346, 1);
 x_349 = x_346;
} else {
 lean_dec_ref(x_346);
 x_349 = lean_box(0);
}
x_350 = lean_array_push(x_36, x_347);
x_351 = lean_box(0);
if (lean_is_scalar(x_349)) {
 x_352 = lean_alloc_ctor(0, 2, 0);
} else {
 x_352 = x_349;
}
lean_ctor_set(x_352, 0, x_35);
lean_ctor_set(x_352, 1, x_350);
x_353 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_353, 0, x_33);
lean_ctor_set(x_353, 1, x_352);
if (lean_is_scalar(x_344)) {
 x_354 = lean_alloc_ctor(0, 2, 0);
} else {
 x_354 = x_344;
}
lean_ctor_set(x_354, 0, x_31);
lean_ctor_set(x_354, 1, x_353);
x_355 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_355, 0, x_351);
lean_ctor_set(x_355, 1, x_354);
x_21 = x_355;
x_22 = x_348;
goto block_27;
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_356 = lean_ctor_get(x_73, 1);
lean_inc(x_356);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_357 = x_73;
} else {
 lean_dec_ref(x_73);
 x_357 = lean_box(0);
}
x_358 = lean_ctor_get(x_215, 0);
lean_inc(x_358);
lean_dec(x_215);
x_359 = lean_ctor_get(x_342, 0);
lean_inc(x_359);
lean_dec(x_342);
x_360 = l_Lean_Meta_SimpExtension_getTheorems___redArg(x_358, x_16, x_356);
lean_dec(x_358);
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_360, 1);
lean_inc(x_362);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 lean_ctor_release(x_360, 1);
 x_363 = x_360;
} else {
 lean_dec_ref(x_360);
 x_363 = lean_box(0);
}
x_364 = l_Lean_Meta_Simp_SimprocExtension_getSimprocs___redArg(x_359, x_16, x_362);
lean_dec(x_359);
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_364, 1);
lean_inc(x_366);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 lean_ctor_release(x_364, 1);
 x_367 = x_364;
} else {
 lean_dec_ref(x_364);
 x_367 = lean_box(0);
}
x_368 = lean_array_push(x_36, x_361);
x_369 = lean_array_push(x_31, x_365);
x_370 = lean_box(0);
if (lean_is_scalar(x_367)) {
 x_371 = lean_alloc_ctor(0, 2, 0);
} else {
 x_371 = x_367;
}
lean_ctor_set(x_371, 0, x_35);
lean_ctor_set(x_371, 1, x_368);
if (lean_is_scalar(x_363)) {
 x_372 = lean_alloc_ctor(0, 2, 0);
} else {
 x_372 = x_363;
}
lean_ctor_set(x_372, 0, x_33);
lean_ctor_set(x_372, 1, x_371);
x_373 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_373, 0, x_369);
lean_ctor_set(x_373, 1, x_372);
if (lean_is_scalar(x_357)) {
 x_374 = lean_alloc_ctor(0, 2, 0);
} else {
 x_374 = x_357;
}
lean_ctor_set(x_374, 0, x_370);
lean_ctor_set(x_374, 1, x_373);
x_21 = x_374;
x_22 = x_366;
goto block_27;
}
}
}
}
}
}
else
{
lean_object* x_375; lean_object* x_376; 
lean_dec(x_72);
lean_dec(x_30);
x_375 = lean_ctor_get(x_73, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_73, 1);
lean_inc(x_376);
lean_dec(x_73);
x_61 = x_68;
x_62 = x_375;
x_63 = x_376;
goto block_66;
}
}
block_384:
{
lean_object* x_382; uint8_t x_383; 
x_382 = l_Lean_Syntax_getArg(x_30, x_20);
x_383 = l_Lean_Syntax_isNone(x_382);
lean_dec(x_382);
if (x_383 == 0)
{
x_67 = x_378;
x_68 = x_379;
x_69 = x_381;
x_70 = x_380;
goto block_377;
}
else
{
x_67 = x_378;
x_68 = x_379;
x_69 = x_381;
x_70 = x_28;
goto block_377;
}
}
block_391:
{
if (lean_obj_tag(x_386) == 0)
{
lean_object* x_387; lean_object* x_388; 
lean_dec(x_385);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_386, 1);
lean_inc(x_388);
lean_dec(x_386);
x_21 = x_387;
x_22 = x_388;
goto block_27;
}
else
{
lean_object* x_389; lean_object* x_390; 
x_389 = lean_ctor_get(x_386, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_386, 1);
lean_inc(x_390);
lean_dec(x_386);
x_61 = x_385;
x_62 = x_389;
x_63 = x_390;
goto block_66;
}
}
block_400:
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; uint8_t x_398; lean_object* x_399; 
x_394 = l_Lean_Syntax_getArg(x_30, x_20);
lean_inc(x_15);
lean_inc(x_13);
x_395 = l_Lean_Elab_Term_isLocalIdent_x3f(x_394, x_11, x_12, x_13, x_14, x_15, x_16, x_392);
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_395, 1);
lean_inc(x_397);
lean_dec(x_395);
x_398 = lean_unbox(x_33);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_35);
lean_inc(x_31);
lean_inc(x_36);
x_399 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_spec__5_spec__5___lam__0(x_30, x_20, x_1, x_18, x_28, x_36, x_398, x_31, x_35, x_396, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_397);
lean_dec(x_30);
x_385 = x_393;
x_386 = x_399;
goto block_391;
}
block_465:
{
lean_object* x_406; 
x_406 = l_Lean_Elab_Tactic_saveState___redArg(x_10, x_12, x_14, x_15, x_16, x_17);
if (x_405 == 0)
{
uint8_t x_407; 
x_407 = !lean_is_exclusive(x_406);
if (x_407 == 0)
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; uint8_t x_412; 
x_408 = lean_ctor_get(x_406, 0);
x_409 = lean_ctor_get(x_406, 1);
x_410 = lean_mk_string_unchecked("simpLemma", 9, 9);
lean_inc(x_404);
lean_inc(x_403);
lean_inc(x_402);
x_411 = l_Lean_Name_mkStr4(x_402, x_403, x_404, x_410);
x_412 = lean_name_eq(x_401, x_411);
lean_dec(x_411);
if (x_412 == 0)
{
lean_object* x_413; lean_object* x_414; uint8_t x_415; 
lean_dec(x_30);
x_413 = lean_mk_string_unchecked("simpStar", 8, 8);
x_414 = l_Lean_Name_mkStr4(x_402, x_403, x_404, x_413);
x_415 = lean_name_eq(x_401, x_414);
lean_dec(x_414);
lean_dec(x_401);
if (x_415 == 0)
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; 
lean_free_object(x_406);
x_416 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_409);
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_416, 1);
lean_inc(x_418);
lean_dec(x_416);
x_61 = x_408;
x_62 = x_417;
x_63 = x_418;
goto block_66;
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
lean_dec(x_408);
lean_dec(x_33);
x_419 = lean_box(0);
lean_ctor_set(x_406, 1, x_36);
lean_ctor_set(x_406, 0, x_35);
x_420 = lean_box(x_415);
x_421 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_421, 0, x_420);
lean_ctor_set(x_421, 1, x_406);
x_422 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_422, 0, x_31);
lean_ctor_set(x_422, 1, x_421);
x_423 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_423, 0, x_419);
lean_ctor_set(x_423, 1, x_422);
x_21 = x_423;
x_22 = x_409;
goto block_27;
}
}
else
{
lean_object* x_424; uint8_t x_425; 
lean_free_object(x_406);
lean_dec(x_401);
x_424 = l_Lean_Syntax_getArg(x_30, x_29);
x_425 = l_Lean_Syntax_isNone(x_424);
if (x_425 == 0)
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; uint8_t x_430; 
x_426 = l_Lean_Syntax_getArg(x_424, x_29);
lean_dec(x_424);
x_427 = l_Lean_Syntax_getKind(x_426);
x_428 = lean_mk_string_unchecked("simpPost", 8, 8);
x_429 = l_Lean_Name_mkStr4(x_402, x_403, x_404, x_428);
x_430 = lean_name_eq(x_427, x_429);
lean_dec(x_429);
lean_dec(x_427);
x_378 = x_409;
x_379 = x_408;
x_380 = x_412;
x_381 = x_430;
goto block_384;
}
else
{
lean_dec(x_424);
lean_dec(x_404);
lean_dec(x_403);
lean_dec(x_402);
x_378 = x_409;
x_379 = x_408;
x_380 = x_412;
x_381 = x_18;
goto block_384;
}
}
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; uint8_t x_435; 
x_431 = lean_ctor_get(x_406, 0);
x_432 = lean_ctor_get(x_406, 1);
lean_inc(x_432);
lean_inc(x_431);
lean_dec(x_406);
x_433 = lean_mk_string_unchecked("simpLemma", 9, 9);
lean_inc(x_404);
lean_inc(x_403);
lean_inc(x_402);
x_434 = l_Lean_Name_mkStr4(x_402, x_403, x_404, x_433);
x_435 = lean_name_eq(x_401, x_434);
lean_dec(x_434);
if (x_435 == 0)
{
lean_object* x_436; lean_object* x_437; uint8_t x_438; 
lean_dec(x_30);
x_436 = lean_mk_string_unchecked("simpStar", 8, 8);
x_437 = l_Lean_Name_mkStr4(x_402, x_403, x_404, x_436);
x_438 = lean_name_eq(x_401, x_437);
lean_dec(x_437);
lean_dec(x_401);
if (x_438 == 0)
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_439 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_432);
x_440 = lean_ctor_get(x_439, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_439, 1);
lean_inc(x_441);
lean_dec(x_439);
x_61 = x_431;
x_62 = x_440;
x_63 = x_441;
goto block_66;
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; 
lean_dec(x_431);
lean_dec(x_33);
x_442 = lean_box(0);
x_443 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_443, 0, x_35);
lean_ctor_set(x_443, 1, x_36);
x_444 = lean_box(x_438);
x_445 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_445, 0, x_444);
lean_ctor_set(x_445, 1, x_443);
x_446 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_446, 0, x_31);
lean_ctor_set(x_446, 1, x_445);
x_447 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_447, 0, x_442);
lean_ctor_set(x_447, 1, x_446);
x_21 = x_447;
x_22 = x_432;
goto block_27;
}
}
else
{
lean_object* x_448; uint8_t x_449; 
lean_dec(x_401);
x_448 = l_Lean_Syntax_getArg(x_30, x_29);
x_449 = l_Lean_Syntax_isNone(x_448);
if (x_449 == 0)
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; uint8_t x_454; 
x_450 = l_Lean_Syntax_getArg(x_448, x_29);
lean_dec(x_448);
x_451 = l_Lean_Syntax_getKind(x_450);
x_452 = lean_mk_string_unchecked("simpPost", 8, 8);
x_453 = l_Lean_Name_mkStr4(x_402, x_403, x_404, x_452);
x_454 = lean_name_eq(x_451, x_453);
lean_dec(x_453);
lean_dec(x_451);
x_378 = x_432;
x_379 = x_431;
x_380 = x_435;
x_381 = x_454;
goto block_384;
}
else
{
lean_dec(x_448);
lean_dec(x_404);
lean_dec(x_403);
lean_dec(x_402);
x_378 = x_432;
x_379 = x_431;
x_380 = x_435;
x_381 = x_18;
goto block_384;
}
}
}
}
else
{
lean_dec(x_404);
lean_dec(x_403);
lean_dec(x_402);
lean_dec(x_401);
if (x_4 == 0)
{
uint8_t x_455; 
x_455 = lean_unbox(x_33);
if (x_455 == 0)
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; uint8_t x_459; lean_object* x_460; 
x_456 = lean_ctor_get(x_406, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_406, 1);
lean_inc(x_457);
lean_dec(x_406);
x_458 = lean_box(0);
x_459 = lean_unbox(x_33);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_35);
lean_inc(x_31);
lean_inc(x_36);
x_460 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_spec__5_spec__5___lam__0(x_30, x_20, x_1, x_18, x_28, x_36, x_459, x_31, x_35, x_458, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_457);
lean_dec(x_30);
x_385 = x_456;
x_386 = x_460;
goto block_391;
}
else
{
lean_object* x_461; lean_object* x_462; 
x_461 = lean_ctor_get(x_406, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_406, 1);
lean_inc(x_462);
lean_dec(x_406);
x_392 = x_462;
x_393 = x_461;
goto block_400;
}
}
else
{
lean_object* x_463; lean_object* x_464; 
x_463 = lean_ctor_get(x_406, 0);
lean_inc(x_463);
x_464 = lean_ctor_get(x_406, 1);
lean_inc(x_464);
lean_dec(x_406);
x_392 = x_464;
x_393 = x_463;
goto block_400;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_spec__5(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_7, x_6);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_70; uint8_t x_378; lean_object* x_379; lean_object* x_380; uint8_t x_381; lean_object* x_385; lean_object* x_386; lean_object* x_392; lean_object* x_393; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; uint8_t x_405; lean_object* x_466; lean_object* x_467; uint8_t x_468; 
x_20 = lean_unsigned_to_nat(1u);
x_28 = l_Lean_Syntax_isNone(x_2);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_array_uget(x_5, x_7);
x_31 = lean_ctor_get(x_8, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_8, 1);
lean_inc(x_32);
lean_dec(x_8);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_30);
x_401 = l_Lean_Syntax_getKind(x_30);
x_402 = lean_mk_string_unchecked("Lean", 4, 4);
x_403 = lean_mk_string_unchecked("Parser", 6, 6);
x_404 = lean_mk_string_unchecked("Tactic", 6, 6);
x_466 = lean_mk_string_unchecked("simpErase", 9, 9);
lean_inc(x_404);
lean_inc(x_403);
lean_inc(x_402);
x_467 = l_Lean_Name_mkStr4(x_402, x_403, x_404, x_466);
x_468 = lean_name_eq(x_401, x_467);
lean_dec(x_467);
if (x_468 == 0)
{
x_405 = x_468;
goto block_465;
}
else
{
x_405 = x_18;
goto block_465;
}
block_27:
{
lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_usize_of_nat(x_20);
x_25 = lean_usize_add(x_7, x_24);
x_26 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_spec__5_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_25, x_23, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_22);
return x_26;
}
block_60:
{
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = l_Lean_Elab_Tactic_SavedState_restore(x_37, x_40, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_38);
x_42 = lean_ctor_get_uint8(x_9, sizeof(void*)*1);
if (x_42 == 0)
{
uint8_t x_43; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_43 = !lean_is_exclusive(x_41);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_41, 0);
lean_dec(x_44);
lean_ctor_set_tag(x_41, 1);
lean_ctor_set(x_41, 0, x_39);
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_dec(x_41);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_39);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_41, 1);
lean_inc(x_47);
lean_dec(x_41);
lean_inc(x_15);
x_48 = l_Lean_Elab_logException___at___Lean_Elab_Tactic_closeUsingOrAdmit_spec__0(x_39, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_35);
lean_ctor_set(x_51, 1, x_36);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_33);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_31);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_49);
lean_ctor_set(x_54, 1, x_53);
x_21 = x_54;
x_22 = x_50;
goto block_27;
}
else
{
uint8_t x_55; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_55 = !lean_is_exclusive(x_48);
if (x_55 == 0)
{
return x_48;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_48, 0);
x_57 = lean_ctor_get(x_48, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_48);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
else
{
lean_object* x_59; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_39);
lean_ctor_set(x_59, 1, x_38);
return x_59;
}
}
block_66:
{
uint8_t x_64; 
x_64 = l_Lean_Exception_isInterrupt(x_62);
if (x_64 == 0)
{
uint8_t x_65; 
x_65 = l_Lean_Exception_isRuntime(x_62);
x_37 = x_61;
x_38 = x_63;
x_39 = x_62;
x_40 = x_65;
goto block_60;
}
else
{
x_37 = x_61;
x_38 = x_63;
x_39 = x_62;
x_40 = x_64;
goto block_60;
}
}
block_377:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_unsigned_to_nat(2u);
x_72 = l_Lean_Syntax_getArg(x_30, x_71);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_72);
x_73 = l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f(x_72, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_68);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
switch (lean_obj_tag(x_74)) {
case 0:
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_73);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_76 = lean_ctor_get(x_73, 1);
x_77 = lean_ctor_get(x_73, 0);
lean_dec(x_77);
x_78 = l_Lean_mkFreshId___at___Lean_Elab_Tactic_elabSimpArgs_spec__4___redArg(x_16, x_76);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_78, 1);
x_81 = lean_ctor_get(x_1, 4);
lean_ctor_set_tag(x_78, 2);
lean_ctor_set(x_78, 1, x_30);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_35);
x_82 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addSimpTheorem(x_81, x_35, x_78, x_72, x_69, x_70, x_11, x_12, x_13, x_14, x_15, x_16, x_80);
if (lean_obj_tag(x_82) == 0)
{
uint8_t x_83; 
lean_dec(x_67);
lean_dec(x_35);
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_82, 1);
x_85 = lean_box(0);
lean_ctor_set(x_82, 1, x_36);
lean_ctor_set(x_73, 1, x_82);
lean_ctor_set(x_73, 0, x_33);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_31);
lean_ctor_set(x_86, 1, x_73);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_21 = x_87;
x_22 = x_84;
goto block_27;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_88 = lean_ctor_get(x_82, 0);
x_89 = lean_ctor_get(x_82, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_82);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_36);
lean_ctor_set(x_73, 1, x_91);
lean_ctor_set(x_73, 0, x_33);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_31);
lean_ctor_set(x_92, 1, x_73);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_92);
x_21 = x_93;
x_22 = x_89;
goto block_27;
}
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_free_object(x_73);
x_94 = lean_ctor_get(x_82, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_82, 1);
lean_inc(x_95);
lean_dec(x_82);
x_61 = x_67;
x_62 = x_94;
x_63 = x_95;
goto block_66;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_ctor_get(x_78, 0);
x_97 = lean_ctor_get(x_78, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_78);
x_98 = lean_ctor_get(x_1, 4);
x_99 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_30);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_35);
x_100 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addSimpTheorem(x_98, x_35, x_99, x_72, x_69, x_70, x_11, x_12, x_13, x_14, x_15, x_16, x_97);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_67);
lean_dec(x_35);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_103 = x_100;
} else {
 lean_dec_ref(x_100);
 x_103 = lean_box(0);
}
x_104 = lean_box(0);
if (lean_is_scalar(x_103)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_103;
}
lean_ctor_set(x_105, 0, x_101);
lean_ctor_set(x_105, 1, x_36);
lean_ctor_set(x_73, 1, x_105);
lean_ctor_set(x_73, 0, x_33);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_31);
lean_ctor_set(x_106, 1, x_73);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_106);
x_21 = x_107;
x_22 = x_102;
goto block_27;
}
else
{
lean_object* x_108; lean_object* x_109; 
lean_free_object(x_73);
x_108 = lean_ctor_get(x_100, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_100, 1);
lean_inc(x_109);
lean_dec(x_100);
x_61 = x_67;
x_62 = x_108;
x_63 = x_109;
goto block_66;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_110 = lean_ctor_get(x_73, 1);
lean_inc(x_110);
lean_dec(x_73);
x_111 = l_Lean_mkFreshId___at___Lean_Elab_Tactic_elabSimpArgs_spec__4___redArg(x_16, x_110);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_114 = x_111;
} else {
 lean_dec_ref(x_111);
 x_114 = lean_box(0);
}
x_115 = lean_ctor_get(x_1, 4);
if (lean_is_scalar(x_114)) {
 x_116 = lean_alloc_ctor(2, 2, 0);
} else {
 x_116 = x_114;
 lean_ctor_set_tag(x_116, 2);
}
lean_ctor_set(x_116, 0, x_112);
lean_ctor_set(x_116, 1, x_30);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_35);
x_117 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addSimpTheorem(x_115, x_35, x_116, x_72, x_69, x_70, x_11, x_12, x_13, x_14, x_15, x_16, x_113);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_67);
lean_dec(x_35);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_120 = x_117;
} else {
 lean_dec_ref(x_117);
 x_120 = lean_box(0);
}
x_121 = lean_box(0);
if (lean_is_scalar(x_120)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_120;
}
lean_ctor_set(x_122, 0, x_118);
lean_ctor_set(x_122, 1, x_36);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_33);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_31);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_121);
lean_ctor_set(x_125, 1, x_124);
x_21 = x_125;
x_22 = x_119;
goto block_27;
}
else
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_117, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_117, 1);
lean_inc(x_127);
lean_dec(x_117);
x_61 = x_67;
x_62 = x_126;
x_63 = x_127;
goto block_66;
}
}
}
case 1:
{
uint8_t x_128; 
lean_dec(x_72);
x_128 = !lean_is_exclusive(x_73);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_129 = lean_ctor_get(x_73, 1);
x_130 = lean_ctor_get(x_73, 0);
lean_dec(x_130);
x_131 = lean_ctor_get(x_74, 0);
lean_inc(x_131);
lean_dec(x_74);
x_132 = l_Lean_mkFreshId___at___Lean_Elab_Tactic_elabSimpArgs_spec__4___redArg(x_16, x_129);
x_133 = !lean_is_exclusive(x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_132, 1);
x_135 = lean_ctor_get(x_1, 4);
lean_ctor_set_tag(x_132, 2);
lean_ctor_set(x_132, 1, x_30);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_35);
x_136 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem(x_135, x_35, x_132, x_131, x_69, x_70, x_3, x_13, x_14, x_15, x_16, x_134);
if (lean_obj_tag(x_136) == 0)
{
uint8_t x_137; 
lean_dec(x_67);
lean_dec(x_35);
x_137 = !lean_is_exclusive(x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_138 = lean_ctor_get(x_136, 1);
x_139 = lean_box(0);
lean_ctor_set(x_136, 1, x_36);
lean_ctor_set(x_73, 1, x_136);
lean_ctor_set(x_73, 0, x_33);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_31);
lean_ctor_set(x_140, 1, x_73);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
x_21 = x_141;
x_22 = x_138;
goto block_27;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_142 = lean_ctor_get(x_136, 0);
x_143 = lean_ctor_get(x_136, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_136);
x_144 = lean_box(0);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_36);
lean_ctor_set(x_73, 1, x_145);
lean_ctor_set(x_73, 0, x_33);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_31);
lean_ctor_set(x_146, 1, x_73);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_146);
x_21 = x_147;
x_22 = x_143;
goto block_27;
}
}
else
{
lean_object* x_148; lean_object* x_149; 
lean_free_object(x_73);
x_148 = lean_ctor_get(x_136, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_136, 1);
lean_inc(x_149);
lean_dec(x_136);
x_61 = x_67;
x_62 = x_148;
x_63 = x_149;
goto block_66;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_150 = lean_ctor_get(x_132, 0);
x_151 = lean_ctor_get(x_132, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_132);
x_152 = lean_ctor_get(x_1, 4);
x_153 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_30);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_35);
x_154 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem(x_152, x_35, x_153, x_131, x_69, x_70, x_3, x_13, x_14, x_15, x_16, x_151);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_67);
lean_dec(x_35);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_157 = x_154;
} else {
 lean_dec_ref(x_154);
 x_157 = lean_box(0);
}
x_158 = lean_box(0);
if (lean_is_scalar(x_157)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_157;
}
lean_ctor_set(x_159, 0, x_155);
lean_ctor_set(x_159, 1, x_36);
lean_ctor_set(x_73, 1, x_159);
lean_ctor_set(x_73, 0, x_33);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_31);
lean_ctor_set(x_160, 1, x_73);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_160);
x_21 = x_161;
x_22 = x_156;
goto block_27;
}
else
{
lean_object* x_162; lean_object* x_163; 
lean_free_object(x_73);
x_162 = lean_ctor_get(x_154, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_154, 1);
lean_inc(x_163);
lean_dec(x_154);
x_61 = x_67;
x_62 = x_162;
x_63 = x_163;
goto block_66;
}
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_164 = lean_ctor_get(x_73, 1);
lean_inc(x_164);
lean_dec(x_73);
x_165 = lean_ctor_get(x_74, 0);
lean_inc(x_165);
lean_dec(x_74);
x_166 = l_Lean_mkFreshId___at___Lean_Elab_Tactic_elabSimpArgs_spec__4___redArg(x_16, x_164);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_169 = x_166;
} else {
 lean_dec_ref(x_166);
 x_169 = lean_box(0);
}
x_170 = lean_ctor_get(x_1, 4);
if (lean_is_scalar(x_169)) {
 x_171 = lean_alloc_ctor(2, 2, 0);
} else {
 x_171 = x_169;
 lean_ctor_set_tag(x_171, 2);
}
lean_ctor_set(x_171, 0, x_167);
lean_ctor_set(x_171, 1, x_30);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_35);
x_172 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem(x_170, x_35, x_171, x_165, x_69, x_70, x_3, x_13, x_14, x_15, x_16, x_168);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_67);
lean_dec(x_35);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_175 = x_172;
} else {
 lean_dec_ref(x_172);
 x_175 = lean_box(0);
}
x_176 = lean_box(0);
if (lean_is_scalar(x_175)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_175;
}
lean_ctor_set(x_177, 0, x_173);
lean_ctor_set(x_177, 1, x_36);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_33);
lean_ctor_set(x_178, 1, x_177);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_31);
lean_ctor_set(x_179, 1, x_178);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_176);
lean_ctor_set(x_180, 1, x_179);
x_21 = x_180;
x_22 = x_174;
goto block_27;
}
else
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_172, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_172, 1);
lean_inc(x_182);
lean_dec(x_172);
x_61 = x_67;
x_62 = x_181;
x_63 = x_182;
goto block_66;
}
}
}
case 2:
{
uint8_t x_183; 
lean_dec(x_72);
lean_dec(x_30);
x_183 = !lean_is_exclusive(x_73);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_184 = lean_ctor_get(x_73, 1);
x_185 = lean_ctor_get(x_73, 0);
lean_dec(x_185);
x_186 = lean_ctor_get(x_74, 0);
lean_inc(x_186);
lean_dec(x_74);
lean_inc(x_31);
x_187 = l_Lean_Meta_Simp_SimprocsArray_add(x_31, x_186, x_69, x_15, x_16, x_184);
if (lean_obj_tag(x_187) == 0)
{
uint8_t x_188; 
lean_dec(x_67);
lean_dec(x_31);
x_188 = !lean_is_exclusive(x_187);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_189 = lean_ctor_get(x_187, 0);
x_190 = lean_ctor_get(x_187, 1);
x_191 = lean_box(0);
lean_ctor_set(x_187, 1, x_36);
lean_ctor_set(x_187, 0, x_35);
lean_ctor_set(x_73, 1, x_187);
lean_ctor_set(x_73, 0, x_33);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_189);
lean_ctor_set(x_192, 1, x_73);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
x_21 = x_193;
x_22 = x_190;
goto block_27;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_194 = lean_ctor_get(x_187, 0);
x_195 = lean_ctor_get(x_187, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_187);
x_196 = lean_box(0);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_35);
lean_ctor_set(x_197, 1, x_36);
lean_ctor_set(x_73, 1, x_197);
lean_ctor_set(x_73, 0, x_33);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_194);
lean_ctor_set(x_198, 1, x_73);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_196);
lean_ctor_set(x_199, 1, x_198);
x_21 = x_199;
x_22 = x_195;
goto block_27;
}
}
else
{
lean_object* x_200; lean_object* x_201; 
lean_free_object(x_73);
x_200 = lean_ctor_get(x_187, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_187, 1);
lean_inc(x_201);
lean_dec(x_187);
x_61 = x_67;
x_62 = x_200;
x_63 = x_201;
goto block_66;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_73, 1);
lean_inc(x_202);
lean_dec(x_73);
x_203 = lean_ctor_get(x_74, 0);
lean_inc(x_203);
lean_dec(x_74);
lean_inc(x_31);
x_204 = l_Lean_Meta_Simp_SimprocsArray_add(x_31, x_203, x_69, x_15, x_16, x_202);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_67);
lean_dec(x_31);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_207 = x_204;
} else {
 lean_dec_ref(x_204);
 x_207 = lean_box(0);
}
x_208 = lean_box(0);
if (lean_is_scalar(x_207)) {
 x_209 = lean_alloc_ctor(0, 2, 0);
} else {
 x_209 = x_207;
}
lean_ctor_set(x_209, 0, x_35);
lean_ctor_set(x_209, 1, x_36);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_33);
lean_ctor_set(x_210, 1, x_209);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_205);
lean_ctor_set(x_211, 1, x_210);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_208);
lean_ctor_set(x_212, 1, x_211);
x_21 = x_212;
x_22 = x_206;
goto block_27;
}
else
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_ctor_get(x_204, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_204, 1);
lean_inc(x_214);
lean_dec(x_204);
x_61 = x_67;
x_62 = x_213;
x_63 = x_214;
goto block_66;
}
}
}
default: 
{
lean_object* x_215; 
lean_dec(x_72);
lean_dec(x_67);
lean_dec(x_30);
x_215 = lean_ctor_get(x_74, 0);
lean_inc(x_215);
if (lean_obj_tag(x_215) == 0)
{
uint8_t x_216; 
x_216 = !lean_is_exclusive(x_74);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; uint8_t x_219; 
x_217 = lean_ctor_get(x_74, 1);
x_218 = lean_ctor_get(x_74, 0);
lean_dec(x_218);
x_219 = !lean_is_exclusive(x_73);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_220 = lean_ctor_get(x_73, 1);
x_221 = lean_ctor_get(x_73, 0);
lean_dec(x_221);
x_222 = lean_ctor_get(x_217, 0);
lean_inc(x_222);
lean_dec(x_217);
x_223 = l_Lean_Meta_Simp_SimprocExtension_getSimprocs___redArg(x_222, x_16, x_220);
lean_dec(x_222);
x_224 = !lean_is_exclusive(x_223);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_225 = lean_ctor_get(x_223, 0);
x_226 = lean_ctor_get(x_223, 1);
x_227 = lean_array_push(x_31, x_225);
x_228 = lean_box(0);
lean_ctor_set(x_223, 1, x_36);
lean_ctor_set(x_223, 0, x_35);
lean_ctor_set_tag(x_74, 0);
lean_ctor_set(x_74, 1, x_223);
lean_ctor_set(x_74, 0, x_33);
lean_ctor_set(x_73, 1, x_74);
lean_ctor_set(x_73, 0, x_227);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_73);
x_21 = x_229;
x_22 = x_226;
goto block_27;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_230 = lean_ctor_get(x_223, 0);
x_231 = lean_ctor_get(x_223, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_223);
x_232 = lean_array_push(x_31, x_230);
x_233 = lean_box(0);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_35);
lean_ctor_set(x_234, 1, x_36);
lean_ctor_set_tag(x_74, 0);
lean_ctor_set(x_74, 1, x_234);
lean_ctor_set(x_74, 0, x_33);
lean_ctor_set(x_73, 1, x_74);
lean_ctor_set(x_73, 0, x_232);
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_73);
x_21 = x_235;
x_22 = x_231;
goto block_27;
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_236 = lean_ctor_get(x_73, 1);
lean_inc(x_236);
lean_dec(x_73);
x_237 = lean_ctor_get(x_217, 0);
lean_inc(x_237);
lean_dec(x_217);
x_238 = l_Lean_Meta_Simp_SimprocExtension_getSimprocs___redArg(x_237, x_16, x_236);
lean_dec(x_237);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_241 = x_238;
} else {
 lean_dec_ref(x_238);
 x_241 = lean_box(0);
}
x_242 = lean_array_push(x_31, x_239);
x_243 = lean_box(0);
if (lean_is_scalar(x_241)) {
 x_244 = lean_alloc_ctor(0, 2, 0);
} else {
 x_244 = x_241;
}
lean_ctor_set(x_244, 0, x_35);
lean_ctor_set(x_244, 1, x_36);
lean_ctor_set_tag(x_74, 0);
lean_ctor_set(x_74, 1, x_244);
lean_ctor_set(x_74, 0, x_33);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_242);
lean_ctor_set(x_245, 1, x_74);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_243);
lean_ctor_set(x_246, 1, x_245);
x_21 = x_246;
x_22 = x_240;
goto block_27;
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_247 = lean_ctor_get(x_74, 1);
lean_inc(x_247);
lean_dec(x_74);
x_248 = lean_ctor_get(x_73, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_249 = x_73;
} else {
 lean_dec_ref(x_73);
 x_249 = lean_box(0);
}
x_250 = lean_ctor_get(x_247, 0);
lean_inc(x_250);
lean_dec(x_247);
x_251 = l_Lean_Meta_Simp_SimprocExtension_getSimprocs___redArg(x_250, x_16, x_248);
lean_dec(x_250);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 x_254 = x_251;
} else {
 lean_dec_ref(x_251);
 x_254 = lean_box(0);
}
x_255 = lean_array_push(x_31, x_252);
x_256 = lean_box(0);
if (lean_is_scalar(x_254)) {
 x_257 = lean_alloc_ctor(0, 2, 0);
} else {
 x_257 = x_254;
}
lean_ctor_set(x_257, 0, x_35);
lean_ctor_set(x_257, 1, x_36);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_33);
lean_ctor_set(x_258, 1, x_257);
if (lean_is_scalar(x_249)) {
 x_259 = lean_alloc_ctor(0, 2, 0);
} else {
 x_259 = x_249;
}
lean_ctor_set(x_259, 0, x_255);
lean_ctor_set(x_259, 1, x_258);
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_256);
lean_ctor_set(x_260, 1, x_259);
x_21 = x_260;
x_22 = x_253;
goto block_27;
}
}
else
{
uint8_t x_261; 
x_261 = !lean_is_exclusive(x_74);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; 
x_262 = lean_ctor_get(x_74, 1);
x_263 = lean_ctor_get(x_74, 0);
lean_dec(x_263);
if (lean_obj_tag(x_262) == 0)
{
uint8_t x_264; 
x_264 = !lean_is_exclusive(x_73);
if (x_264 == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; 
x_265 = lean_ctor_get(x_73, 1);
x_266 = lean_ctor_get(x_73, 0);
lean_dec(x_266);
x_267 = lean_ctor_get(x_215, 0);
lean_inc(x_267);
lean_dec(x_215);
x_268 = l_Lean_Meta_SimpExtension_getTheorems___redArg(x_267, x_16, x_265);
lean_dec(x_267);
x_269 = !lean_is_exclusive(x_268);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_270 = lean_ctor_get(x_268, 0);
x_271 = lean_ctor_get(x_268, 1);
x_272 = lean_array_push(x_36, x_270);
x_273 = lean_box(0);
lean_ctor_set(x_268, 1, x_272);
lean_ctor_set(x_268, 0, x_35);
lean_ctor_set_tag(x_74, 0);
lean_ctor_set(x_74, 1, x_268);
lean_ctor_set(x_74, 0, x_33);
lean_ctor_set(x_73, 1, x_74);
lean_ctor_set(x_73, 0, x_31);
x_274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_73);
x_21 = x_274;
x_22 = x_271;
goto block_27;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_275 = lean_ctor_get(x_268, 0);
x_276 = lean_ctor_get(x_268, 1);
lean_inc(x_276);
lean_inc(x_275);
lean_dec(x_268);
x_277 = lean_array_push(x_36, x_275);
x_278 = lean_box(0);
x_279 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_279, 0, x_35);
lean_ctor_set(x_279, 1, x_277);
lean_ctor_set_tag(x_74, 0);
lean_ctor_set(x_74, 1, x_279);
lean_ctor_set(x_74, 0, x_33);
lean_ctor_set(x_73, 1, x_74);
lean_ctor_set(x_73, 0, x_31);
x_280 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_73);
x_21 = x_280;
x_22 = x_276;
goto block_27;
}
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_281 = lean_ctor_get(x_73, 1);
lean_inc(x_281);
lean_dec(x_73);
x_282 = lean_ctor_get(x_215, 0);
lean_inc(x_282);
lean_dec(x_215);
x_283 = l_Lean_Meta_SimpExtension_getTheorems___redArg(x_282, x_16, x_281);
lean_dec(x_282);
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_283, 1);
lean_inc(x_285);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 x_286 = x_283;
} else {
 lean_dec_ref(x_283);
 x_286 = lean_box(0);
}
x_287 = lean_array_push(x_36, x_284);
x_288 = lean_box(0);
if (lean_is_scalar(x_286)) {
 x_289 = lean_alloc_ctor(0, 2, 0);
} else {
 x_289 = x_286;
}
lean_ctor_set(x_289, 0, x_35);
lean_ctor_set(x_289, 1, x_287);
lean_ctor_set_tag(x_74, 0);
lean_ctor_set(x_74, 1, x_289);
lean_ctor_set(x_74, 0, x_33);
x_290 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_290, 0, x_31);
lean_ctor_set(x_290, 1, x_74);
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_288);
lean_ctor_set(x_291, 1, x_290);
x_21 = x_291;
x_22 = x_285;
goto block_27;
}
}
else
{
uint8_t x_292; 
x_292 = !lean_is_exclusive(x_73);
if (x_292 == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; uint8_t x_298; 
x_293 = lean_ctor_get(x_73, 1);
x_294 = lean_ctor_get(x_73, 0);
lean_dec(x_294);
x_295 = lean_ctor_get(x_215, 0);
lean_inc(x_295);
lean_dec(x_215);
x_296 = lean_ctor_get(x_262, 0);
lean_inc(x_296);
lean_dec(x_262);
x_297 = l_Lean_Meta_SimpExtension_getTheorems___redArg(x_295, x_16, x_293);
lean_dec(x_295);
x_298 = !lean_is_exclusive(x_297);
if (x_298 == 0)
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; 
x_299 = lean_ctor_get(x_297, 0);
x_300 = lean_ctor_get(x_297, 1);
x_301 = l_Lean_Meta_Simp_SimprocExtension_getSimprocs___redArg(x_296, x_16, x_300);
lean_dec(x_296);
x_302 = !lean_is_exclusive(x_301);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_303 = lean_ctor_get(x_301, 0);
x_304 = lean_ctor_get(x_301, 1);
x_305 = lean_array_push(x_36, x_299);
x_306 = lean_array_push(x_31, x_303);
x_307 = lean_box(0);
lean_ctor_set(x_301, 1, x_305);
lean_ctor_set(x_301, 0, x_35);
lean_ctor_set(x_297, 1, x_301);
lean_ctor_set(x_297, 0, x_33);
lean_ctor_set_tag(x_74, 0);
lean_ctor_set(x_74, 1, x_297);
lean_ctor_set(x_74, 0, x_306);
lean_ctor_set(x_73, 1, x_74);
lean_ctor_set(x_73, 0, x_307);
x_21 = x_73;
x_22 = x_304;
goto block_27;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_308 = lean_ctor_get(x_301, 0);
x_309 = lean_ctor_get(x_301, 1);
lean_inc(x_309);
lean_inc(x_308);
lean_dec(x_301);
x_310 = lean_array_push(x_36, x_299);
x_311 = lean_array_push(x_31, x_308);
x_312 = lean_box(0);
x_313 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_313, 0, x_35);
lean_ctor_set(x_313, 1, x_310);
lean_ctor_set(x_297, 1, x_313);
lean_ctor_set(x_297, 0, x_33);
lean_ctor_set_tag(x_74, 0);
lean_ctor_set(x_74, 1, x_297);
lean_ctor_set(x_74, 0, x_311);
lean_ctor_set(x_73, 1, x_74);
lean_ctor_set(x_73, 0, x_312);
x_21 = x_73;
x_22 = x_309;
goto block_27;
}
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_314 = lean_ctor_get(x_297, 0);
x_315 = lean_ctor_get(x_297, 1);
lean_inc(x_315);
lean_inc(x_314);
lean_dec(x_297);
x_316 = l_Lean_Meta_Simp_SimprocExtension_getSimprocs___redArg(x_296, x_16, x_315);
lean_dec(x_296);
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_316, 1);
lean_inc(x_318);
if (lean_is_exclusive(x_316)) {
 lean_ctor_release(x_316, 0);
 lean_ctor_release(x_316, 1);
 x_319 = x_316;
} else {
 lean_dec_ref(x_316);
 x_319 = lean_box(0);
}
x_320 = lean_array_push(x_36, x_314);
x_321 = lean_array_push(x_31, x_317);
x_322 = lean_box(0);
if (lean_is_scalar(x_319)) {
 x_323 = lean_alloc_ctor(0, 2, 0);
} else {
 x_323 = x_319;
}
lean_ctor_set(x_323, 0, x_35);
lean_ctor_set(x_323, 1, x_320);
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_33);
lean_ctor_set(x_324, 1, x_323);
lean_ctor_set_tag(x_74, 0);
lean_ctor_set(x_74, 1, x_324);
lean_ctor_set(x_74, 0, x_321);
lean_ctor_set(x_73, 1, x_74);
lean_ctor_set(x_73, 0, x_322);
x_21 = x_73;
x_22 = x_318;
goto block_27;
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_325 = lean_ctor_get(x_73, 1);
lean_inc(x_325);
lean_dec(x_73);
x_326 = lean_ctor_get(x_215, 0);
lean_inc(x_326);
lean_dec(x_215);
x_327 = lean_ctor_get(x_262, 0);
lean_inc(x_327);
lean_dec(x_262);
x_328 = l_Lean_Meta_SimpExtension_getTheorems___redArg(x_326, x_16, x_325);
lean_dec(x_326);
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_328, 1);
lean_inc(x_330);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 lean_ctor_release(x_328, 1);
 x_331 = x_328;
} else {
 lean_dec_ref(x_328);
 x_331 = lean_box(0);
}
x_332 = l_Lean_Meta_Simp_SimprocExtension_getSimprocs___redArg(x_327, x_16, x_330);
lean_dec(x_327);
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_332, 1);
lean_inc(x_334);
if (lean_is_exclusive(x_332)) {
 lean_ctor_release(x_332, 0);
 lean_ctor_release(x_332, 1);
 x_335 = x_332;
} else {
 lean_dec_ref(x_332);
 x_335 = lean_box(0);
}
x_336 = lean_array_push(x_36, x_329);
x_337 = lean_array_push(x_31, x_333);
x_338 = lean_box(0);
if (lean_is_scalar(x_335)) {
 x_339 = lean_alloc_ctor(0, 2, 0);
} else {
 x_339 = x_335;
}
lean_ctor_set(x_339, 0, x_35);
lean_ctor_set(x_339, 1, x_336);
if (lean_is_scalar(x_331)) {
 x_340 = lean_alloc_ctor(0, 2, 0);
} else {
 x_340 = x_331;
}
lean_ctor_set(x_340, 0, x_33);
lean_ctor_set(x_340, 1, x_339);
lean_ctor_set_tag(x_74, 0);
lean_ctor_set(x_74, 1, x_340);
lean_ctor_set(x_74, 0, x_337);
x_341 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_341, 0, x_338);
lean_ctor_set(x_341, 1, x_74);
x_21 = x_341;
x_22 = x_334;
goto block_27;
}
}
}
else
{
lean_object* x_342; 
x_342 = lean_ctor_get(x_74, 1);
lean_inc(x_342);
lean_dec(x_74);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_343 = lean_ctor_get(x_73, 1);
lean_inc(x_343);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_344 = x_73;
} else {
 lean_dec_ref(x_73);
 x_344 = lean_box(0);
}
x_345 = lean_ctor_get(x_215, 0);
lean_inc(x_345);
lean_dec(x_215);
x_346 = l_Lean_Meta_SimpExtension_getTheorems___redArg(x_345, x_16, x_343);
lean_dec(x_345);
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_346, 1);
lean_inc(x_348);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 lean_ctor_release(x_346, 1);
 x_349 = x_346;
} else {
 lean_dec_ref(x_346);
 x_349 = lean_box(0);
}
x_350 = lean_array_push(x_36, x_347);
x_351 = lean_box(0);
if (lean_is_scalar(x_349)) {
 x_352 = lean_alloc_ctor(0, 2, 0);
} else {
 x_352 = x_349;
}
lean_ctor_set(x_352, 0, x_35);
lean_ctor_set(x_352, 1, x_350);
x_353 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_353, 0, x_33);
lean_ctor_set(x_353, 1, x_352);
if (lean_is_scalar(x_344)) {
 x_354 = lean_alloc_ctor(0, 2, 0);
} else {
 x_354 = x_344;
}
lean_ctor_set(x_354, 0, x_31);
lean_ctor_set(x_354, 1, x_353);
x_355 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_355, 0, x_351);
lean_ctor_set(x_355, 1, x_354);
x_21 = x_355;
x_22 = x_348;
goto block_27;
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_356 = lean_ctor_get(x_73, 1);
lean_inc(x_356);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_357 = x_73;
} else {
 lean_dec_ref(x_73);
 x_357 = lean_box(0);
}
x_358 = lean_ctor_get(x_215, 0);
lean_inc(x_358);
lean_dec(x_215);
x_359 = lean_ctor_get(x_342, 0);
lean_inc(x_359);
lean_dec(x_342);
x_360 = l_Lean_Meta_SimpExtension_getTheorems___redArg(x_358, x_16, x_356);
lean_dec(x_358);
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_360, 1);
lean_inc(x_362);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 lean_ctor_release(x_360, 1);
 x_363 = x_360;
} else {
 lean_dec_ref(x_360);
 x_363 = lean_box(0);
}
x_364 = l_Lean_Meta_Simp_SimprocExtension_getSimprocs___redArg(x_359, x_16, x_362);
lean_dec(x_359);
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_364, 1);
lean_inc(x_366);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 lean_ctor_release(x_364, 1);
 x_367 = x_364;
} else {
 lean_dec_ref(x_364);
 x_367 = lean_box(0);
}
x_368 = lean_array_push(x_36, x_361);
x_369 = lean_array_push(x_31, x_365);
x_370 = lean_box(0);
if (lean_is_scalar(x_367)) {
 x_371 = lean_alloc_ctor(0, 2, 0);
} else {
 x_371 = x_367;
}
lean_ctor_set(x_371, 0, x_35);
lean_ctor_set(x_371, 1, x_368);
if (lean_is_scalar(x_363)) {
 x_372 = lean_alloc_ctor(0, 2, 0);
} else {
 x_372 = x_363;
}
lean_ctor_set(x_372, 0, x_33);
lean_ctor_set(x_372, 1, x_371);
x_373 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_373, 0, x_369);
lean_ctor_set(x_373, 1, x_372);
if (lean_is_scalar(x_357)) {
 x_374 = lean_alloc_ctor(0, 2, 0);
} else {
 x_374 = x_357;
}
lean_ctor_set(x_374, 0, x_370);
lean_ctor_set(x_374, 1, x_373);
x_21 = x_374;
x_22 = x_366;
goto block_27;
}
}
}
}
}
}
else
{
lean_object* x_375; lean_object* x_376; 
lean_dec(x_72);
lean_dec(x_30);
x_375 = lean_ctor_get(x_73, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_73, 1);
lean_inc(x_376);
lean_dec(x_73);
x_61 = x_67;
x_62 = x_375;
x_63 = x_376;
goto block_66;
}
}
block_384:
{
lean_object* x_382; uint8_t x_383; 
x_382 = l_Lean_Syntax_getArg(x_30, x_20);
x_383 = l_Lean_Syntax_isNone(x_382);
lean_dec(x_382);
if (x_383 == 0)
{
x_67 = x_380;
x_68 = x_379;
x_69 = x_381;
x_70 = x_378;
goto block_377;
}
else
{
x_67 = x_380;
x_68 = x_379;
x_69 = x_381;
x_70 = x_28;
goto block_377;
}
}
block_391:
{
if (lean_obj_tag(x_386) == 0)
{
lean_object* x_387; lean_object* x_388; 
lean_dec(x_385);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_386, 1);
lean_inc(x_388);
lean_dec(x_386);
x_21 = x_387;
x_22 = x_388;
goto block_27;
}
else
{
lean_object* x_389; lean_object* x_390; 
x_389 = lean_ctor_get(x_386, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_386, 1);
lean_inc(x_390);
lean_dec(x_386);
x_61 = x_385;
x_62 = x_389;
x_63 = x_390;
goto block_66;
}
}
block_400:
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; uint8_t x_398; lean_object* x_399; 
x_394 = l_Lean_Syntax_getArg(x_30, x_20);
lean_inc(x_15);
lean_inc(x_13);
x_395 = l_Lean_Elab_Term_isLocalIdent_x3f(x_394, x_11, x_12, x_13, x_14, x_15, x_16, x_393);
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_395, 1);
lean_inc(x_397);
lean_dec(x_395);
x_398 = lean_unbox(x_33);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_35);
lean_inc(x_31);
lean_inc(x_36);
x_399 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_spec__5_spec__5___lam__0(x_30, x_20, x_1, x_18, x_28, x_36, x_398, x_31, x_35, x_396, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_397);
lean_dec(x_30);
x_385 = x_392;
x_386 = x_399;
goto block_391;
}
block_465:
{
lean_object* x_406; 
x_406 = l_Lean_Elab_Tactic_saveState___redArg(x_10, x_12, x_14, x_15, x_16, x_17);
if (x_405 == 0)
{
uint8_t x_407; 
x_407 = !lean_is_exclusive(x_406);
if (x_407 == 0)
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; uint8_t x_412; 
x_408 = lean_ctor_get(x_406, 0);
x_409 = lean_ctor_get(x_406, 1);
x_410 = lean_mk_string_unchecked("simpLemma", 9, 9);
lean_inc(x_404);
lean_inc(x_403);
lean_inc(x_402);
x_411 = l_Lean_Name_mkStr4(x_402, x_403, x_404, x_410);
x_412 = lean_name_eq(x_401, x_411);
lean_dec(x_411);
if (x_412 == 0)
{
lean_object* x_413; lean_object* x_414; uint8_t x_415; 
lean_dec(x_30);
x_413 = lean_mk_string_unchecked("simpStar", 8, 8);
x_414 = l_Lean_Name_mkStr4(x_402, x_403, x_404, x_413);
x_415 = lean_name_eq(x_401, x_414);
lean_dec(x_414);
lean_dec(x_401);
if (x_415 == 0)
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; 
lean_free_object(x_406);
x_416 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_409);
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_416, 1);
lean_inc(x_418);
lean_dec(x_416);
x_61 = x_408;
x_62 = x_417;
x_63 = x_418;
goto block_66;
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
lean_dec(x_408);
lean_dec(x_33);
x_419 = lean_box(0);
lean_ctor_set(x_406, 1, x_36);
lean_ctor_set(x_406, 0, x_35);
x_420 = lean_box(x_415);
x_421 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_421, 0, x_420);
lean_ctor_set(x_421, 1, x_406);
x_422 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_422, 0, x_31);
lean_ctor_set(x_422, 1, x_421);
x_423 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_423, 0, x_419);
lean_ctor_set(x_423, 1, x_422);
x_21 = x_423;
x_22 = x_409;
goto block_27;
}
}
else
{
lean_object* x_424; uint8_t x_425; 
lean_free_object(x_406);
lean_dec(x_401);
x_424 = l_Lean_Syntax_getArg(x_30, x_29);
x_425 = l_Lean_Syntax_isNone(x_424);
if (x_425 == 0)
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; uint8_t x_430; 
x_426 = l_Lean_Syntax_getArg(x_424, x_29);
lean_dec(x_424);
x_427 = l_Lean_Syntax_getKind(x_426);
x_428 = lean_mk_string_unchecked("simpPost", 8, 8);
x_429 = l_Lean_Name_mkStr4(x_402, x_403, x_404, x_428);
x_430 = lean_name_eq(x_427, x_429);
lean_dec(x_429);
lean_dec(x_427);
x_378 = x_412;
x_379 = x_409;
x_380 = x_408;
x_381 = x_430;
goto block_384;
}
else
{
lean_dec(x_424);
lean_dec(x_404);
lean_dec(x_403);
lean_dec(x_402);
x_378 = x_412;
x_379 = x_409;
x_380 = x_408;
x_381 = x_18;
goto block_384;
}
}
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; uint8_t x_435; 
x_431 = lean_ctor_get(x_406, 0);
x_432 = lean_ctor_get(x_406, 1);
lean_inc(x_432);
lean_inc(x_431);
lean_dec(x_406);
x_433 = lean_mk_string_unchecked("simpLemma", 9, 9);
lean_inc(x_404);
lean_inc(x_403);
lean_inc(x_402);
x_434 = l_Lean_Name_mkStr4(x_402, x_403, x_404, x_433);
x_435 = lean_name_eq(x_401, x_434);
lean_dec(x_434);
if (x_435 == 0)
{
lean_object* x_436; lean_object* x_437; uint8_t x_438; 
lean_dec(x_30);
x_436 = lean_mk_string_unchecked("simpStar", 8, 8);
x_437 = l_Lean_Name_mkStr4(x_402, x_403, x_404, x_436);
x_438 = lean_name_eq(x_401, x_437);
lean_dec(x_437);
lean_dec(x_401);
if (x_438 == 0)
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_439 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_432);
x_440 = lean_ctor_get(x_439, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_439, 1);
lean_inc(x_441);
lean_dec(x_439);
x_61 = x_431;
x_62 = x_440;
x_63 = x_441;
goto block_66;
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; 
lean_dec(x_431);
lean_dec(x_33);
x_442 = lean_box(0);
x_443 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_443, 0, x_35);
lean_ctor_set(x_443, 1, x_36);
x_444 = lean_box(x_438);
x_445 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_445, 0, x_444);
lean_ctor_set(x_445, 1, x_443);
x_446 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_446, 0, x_31);
lean_ctor_set(x_446, 1, x_445);
x_447 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_447, 0, x_442);
lean_ctor_set(x_447, 1, x_446);
x_21 = x_447;
x_22 = x_432;
goto block_27;
}
}
else
{
lean_object* x_448; uint8_t x_449; 
lean_dec(x_401);
x_448 = l_Lean_Syntax_getArg(x_30, x_29);
x_449 = l_Lean_Syntax_isNone(x_448);
if (x_449 == 0)
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; uint8_t x_454; 
x_450 = l_Lean_Syntax_getArg(x_448, x_29);
lean_dec(x_448);
x_451 = l_Lean_Syntax_getKind(x_450);
x_452 = lean_mk_string_unchecked("simpPost", 8, 8);
x_453 = l_Lean_Name_mkStr4(x_402, x_403, x_404, x_452);
x_454 = lean_name_eq(x_451, x_453);
lean_dec(x_453);
lean_dec(x_451);
x_378 = x_435;
x_379 = x_432;
x_380 = x_431;
x_381 = x_454;
goto block_384;
}
else
{
lean_dec(x_448);
lean_dec(x_404);
lean_dec(x_403);
lean_dec(x_402);
x_378 = x_435;
x_379 = x_432;
x_380 = x_431;
x_381 = x_18;
goto block_384;
}
}
}
}
else
{
lean_dec(x_404);
lean_dec(x_403);
lean_dec(x_402);
lean_dec(x_401);
if (x_4 == 0)
{
uint8_t x_455; 
x_455 = lean_unbox(x_33);
if (x_455 == 0)
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; uint8_t x_459; lean_object* x_460; 
x_456 = lean_ctor_get(x_406, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_406, 1);
lean_inc(x_457);
lean_dec(x_406);
x_458 = lean_box(0);
x_459 = lean_unbox(x_33);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_35);
lean_inc(x_31);
lean_inc(x_36);
x_460 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_spec__5_spec__5___lam__0(x_30, x_20, x_1, x_18, x_28, x_36, x_459, x_31, x_35, x_458, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_457);
lean_dec(x_30);
x_385 = x_456;
x_386 = x_460;
goto block_391;
}
else
{
lean_object* x_461; lean_object* x_462; 
x_461 = lean_ctor_get(x_406, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_406, 1);
lean_inc(x_462);
lean_dec(x_406);
x_392 = x_461;
x_393 = x_462;
goto block_400;
}
}
else
{
lean_object* x_463; lean_object* x_464; 
x_463 = lean_ctor_get(x_406, 0);
lean_inc(x_463);
x_464 = lean_ctor_get(x_406, 1);
lean_inc(x_464);
lean_dec(x_406);
x_392 = x_463;
x_393 = x_464;
goto block_400;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withTrackingZetaDeltaSet___at___Lean_Elab_Tactic_elabSimpArgs_spec__7___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_st_ref_take(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 4);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_2);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withTrackingZetaDeltaSet___at___Lean_Elab_Tactic_elabSimpArgs_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_12; 
x_12 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint64_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_13 = lean_st_ref_get(x_8, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_take(x_8, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_20);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_inc(x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_20);
lean_inc(x_20);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_20);
lean_inc(x_24);
lean_inc(x_21);
x_25 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_25, 2, x_23);
lean_ctor_set(x_25, 3, x_21);
lean_ctor_set(x_25, 4, x_24);
lean_ctor_set(x_25, 5, x_24);
x_26 = lean_ctor_get(x_17, 2);
lean_inc(x_26);
x_27 = lean_ctor_get(x_17, 3);
lean_inc(x_27);
x_28 = lean_ctor_get(x_17, 4);
lean_inc(x_28);
lean_dec(x_17);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_25);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set(x_29, 3, x_27);
lean_ctor_set(x_29, 4, x_28);
x_30 = lean_st_ref_set(x_8, x_29, x_18);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_box(1);
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
lean_dec(x_14);
x_34 = lean_ctor_get(x_7, 0);
lean_inc(x_34);
x_35 = lean_ctor_get_uint64(x_7, sizeof(void*)*7);
x_36 = lean_ctor_get(x_7, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_7, 3);
lean_inc(x_37);
x_38 = lean_ctor_get(x_7, 4);
lean_inc(x_38);
x_39 = lean_ctor_get(x_7, 5);
lean_inc(x_39);
x_40 = lean_ctor_get(x_7, 6);
lean_inc(x_40);
x_41 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 9);
x_42 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 10);
lean_dec(x_7);
x_43 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_43, 0, x_34);
lean_ctor_set(x_43, 1, x_1);
lean_ctor_set(x_43, 2, x_36);
lean_ctor_set(x_43, 3, x_37);
lean_ctor_set(x_43, 4, x_38);
lean_ctor_set(x_43, 5, x_39);
lean_ctor_set(x_43, 6, x_40);
lean_ctor_set_uint64(x_43, sizeof(void*)*7, x_35);
x_44 = lean_unbox(x_32);
lean_ctor_set_uint8(x_43, sizeof(void*)*7 + 8, x_44);
lean_ctor_set_uint8(x_43, sizeof(void*)*7 + 9, x_41);
lean_ctor_set_uint8(x_43, sizeof(void*)*7 + 10, x_42);
lean_inc(x_8);
x_45 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_43, x_8, x_9, x_10, x_31);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_46);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_46);
x_49 = l_Lean_Meta_withTrackingZetaDeltaSet___at___Lean_Elab_Tactic_elabSimpArgs_spec__7___redArg___lam__0(x_8, x_33, x_48, x_47);
lean_dec(x_48);
lean_dec(x_8);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
lean_ctor_set(x_49, 0, x_46);
return x_49;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_46);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_45, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_45, 1);
lean_inc(x_55);
lean_dec(x_45);
x_56 = lean_box(0);
x_57 = l_Lean_Meta_withTrackingZetaDeltaSet___at___Lean_Elab_Tactic_elabSimpArgs_spec__7___redArg___lam__0(x_8, x_33, x_56, x_55);
lean_dec(x_8);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
lean_ctor_set_tag(x_57, 1);
lean_ctor_set(x_57, 0, x_54);
return x_57;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_54);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withTrackingZetaDeltaSet___at___Lean_Elab_Tactic_elabSimpArgs_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_withTrackingZetaDeltaSet___at___Lean_Elab_Tactic_elabSimpArgs_spec__7___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = lean_array_size(x_1);
x_19 = lean_usize_of_nat(x_2);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_20 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_spec__5(x_3, x_4, x_5, x_6, x_1, x_18, x_19, x_7, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_dec(x_23);
x_29 = l_Lean_Meta_getZetaDeltaFVarIds(x_13, x_14, x_15, x_16, x_24);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = l_Lean_Meta_Simp_Context_setZetaDeltaSet(x_3, x_8, x_31);
x_33 = lean_array_set(x_28, x_2, x_27);
x_34 = l_Lean_Meta_Simp_Context_setSimpTheorems(x_32, x_33);
lean_dec(x_32);
x_35 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_25);
x_36 = lean_unbox(x_26);
lean_dec(x_26);
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_36);
lean_ctor_set(x_29, 0, x_35);
return x_29;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_37 = lean_ctor_get(x_29, 0);
x_38 = lean_ctor_get(x_29, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_29);
x_39 = l_Lean_Meta_Simp_Context_setZetaDeltaSet(x_3, x_8, x_37);
x_40 = lean_array_set(x_28, x_2, x_27);
x_41 = l_Lean_Meta_Simp_Context_setSimpTheorems(x_39, x_40);
lean_dec(x_39);
x_42 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_25);
x_43 = lean_unbox(x_26);
lean_dec(x_26);
lean_ctor_set_uint8(x_42, sizeof(void*)*2, x_43);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_38);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
x_45 = !lean_is_exclusive(x_20);
if (x_45 == 0)
{
return x_20;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_20, 0);
x_47 = lean_ctor_get(x_20, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_20);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_16 = l_Lean_Elab_Tactic_elabSimpArgs_toZetaDeltaSet(x_1, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_2, 5);
lean_inc(x_19);
x_20 = l_Lean_Meta_instInhabitedSimpTheorems;
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_get(x_20, x_19, x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = l_Lean_Syntax_getArg(x_1, x_23);
x_25 = l_Lean_Syntax_getSepArgs(x_24);
lean_dec(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_19);
x_27 = lean_box(x_3);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_4);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_box(x_5);
x_31 = lean_box(x_6);
lean_inc(x_17);
x_32 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabSimpArgs___lam__0___boxed), 17, 8);
lean_closure_set(x_32, 0, x_25);
lean_closure_set(x_32, 1, x_21);
lean_closure_set(x_32, 2, x_2);
lean_closure_set(x_32, 3, x_1);
lean_closure_set(x_32, 4, x_30);
lean_closure_set(x_32, 5, x_31);
lean_closure_set(x_32, 6, x_29);
lean_closure_set(x_32, 7, x_17);
x_33 = l_Lean_Meta_withTrackingZetaDeltaSet___at___Lean_Elab_Tactic_elabSimpArgs_spec__7___redArg(x_17, x_32, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_18);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_16);
if (x_34 == 0)
{
return x_16;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_16, 0);
x_36 = lean_ctor_get(x_16, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_16);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = l_Lean_Syntax_isNone(x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_box(x_15);
x_17 = lean_box(x_5);
x_18 = lean_box(x_4);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabSimpArgs___lam__1___boxed), 15, 6);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_2);
lean_closure_set(x_19, 2, x_16);
lean_closure_set(x_19, 3, x_3);
lean_closure_set(x_19, 4, x_17);
lean_closure_set(x_19, 5, x_18);
x_20 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMainContext___boxed), 11, 2);
lean_closure_set(x_21, 0, lean_box(0));
lean_closure_set(x_21, 1, x_19);
x_22 = l_Lean_Elab_Term_withoutErrToSorry___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery_spec__0(lean_box(0), x_21, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_8);
return x_22;
}
else
{
lean_object* x_23; 
x_23 = l_Lean_Elab_Tactic_withMainContext___redArg(x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_10);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_3);
x_26 = lean_unbox(x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_14);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___Lean_Meta_SimpTheorems_erase___at___Lean_Elab_Tactic_elabSimpArgs_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_logWarning___at___Lean_Meta_SimpTheorems_erase___at___Lean_Elab_Tactic_elabSimpArgs_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at___Lean_Elab_Tactic_elabSimpArgs_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_SimpTheorems_erase___at___Lean_Elab_Tactic_elabSimpArgs_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at___Lean_Elab_Tactic_elabSimpArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_SimpTheorems_erase___at___Lean_Elab_Tactic_elabSimpArgs_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_Elab_Tactic_elabSimpArgs_spec__2_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_Elab_Tactic_elabSimpArgs_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_Elab_Tactic_elabSimpArgs_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_Elab_Tactic_elabSimpArgs_spec__2_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_Elab_Tactic_elabSimpArgs_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwUnknownConstant___at___Lean_Elab_Tactic_elabSimpArgs_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_Elab_Tactic_elabSimpArgs_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwUnknownConstant___at___Lean_Elab_Tactic_elabSimpArgs_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_Elab_Tactic_elabSimpArgs_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at___Lean_Elab_Tactic_elabSimpArgs_spec__4___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_Elab_Tactic_elabSimpArgs_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_mkFreshId___at___Lean_Elab_Tactic_elabSimpArgs_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_spec__5_spec__5___lam__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_20 = lean_unbox(x_4);
lean_dec(x_4);
x_21 = lean_unbox(x_5);
lean_dec(x_5);
x_22 = lean_unbox(x_7);
lean_dec(x_7);
x_23 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_spec__5_spec__5___lam__0(x_1, x_2, x_3, x_20, x_21, x_6, x_22, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_spec__5_spec__5___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; uint8_t x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_18 = lean_unbox(x_3);
lean_dec(x_3);
x_19 = lean_unbox(x_4);
lean_dec(x_4);
x_20 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_21 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_22 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_spec__5_spec__5(x_1, x_2, x_18, x_19, x_5, x_20, x_21, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_spec__5___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; uint8_t x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_18 = lean_unbox(x_3);
lean_dec(x_3);
x_19 = lean_unbox(x_4);
lean_dec(x_4);
x_20 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_21 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_22 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabSimpArgs_spec__5(x_1, x_2, x_18, x_19, x_5, x_20, x_21, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withTrackingZetaDeltaSet___at___Lean_Elab_Tactic_elabSimpArgs_spec__7___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_withTrackingZetaDeltaSet___at___Lean_Elab_Tactic_elabSimpArgs_spec__7___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs___lam__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_unbox(x_5);
lean_dec(x_5);
x_19 = lean_unbox(x_6);
lean_dec(x_6);
x_20 = l_Lean_Elab_Tactic_elabSimpArgs___lam__0(x_1, x_2, x_3, x_4, x_18, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_16 = lean_unbox(x_3);
lean_dec(x_3);
x_17 = lean_unbox(x_5);
lean_dec(x_5);
x_18 = lean_unbox(x_6);
lean_dec(x_6);
x_19 = l_Lean_Elab_Tactic_elabSimpArgs___lam__1(x_1, x_2, x_16, x_4, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = lean_unbox(x_5);
lean_dec(x_5);
x_17 = l_Lean_Elab_Tactic_elabSimpArgs(x_1, x_2, x_3, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_simpParamsPos() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(4u);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_simpOnlyPos() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(3u);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_isSimpOnly(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc(x_1);
x_2 = l_Lean_Syntax_getKind(x_1);
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("simp", 4, 4);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_name_eq(x_2, x_7);
lean_dec(x_7);
lean_dec(x_2);
if (x_8 == 0)
{
lean_dec(x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_unsigned_to_nat(3u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
lean_dec(x_1);
x_11 = l_Lean_Syntax_isNone(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
return x_8;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_isSimpOnly___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Tactic_isSimpOnly(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getSimpParams(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_unsigned_to_nat(4u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_3, x_4);
lean_dec(x_3);
x_6 = l_Lean_Syntax_getSepArgs(x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getSimpParams___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_getSimpParams(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_setSimpParams(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Array_isEmpty___redArg(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_4 = lean_mk_string_unchecked("[", 1, 1);
x_5 = l_Lean_mkAtom(x_4);
x_6 = lean_mk_string_unchecked(",", 1, 1);
x_7 = l_Lean_mkAtom(x_6);
x_8 = l_Lean_Syntax_mkSep(x_2, x_7);
x_9 = lean_mk_string_unchecked("]", 1, 1);
x_10 = l_Lean_mkAtom(x_9);
x_11 = lean_unsigned_to_nat(3u);
x_12 = lean_mk_empty_array_with_capacity(x_11);
x_13 = lean_array_push(x_12, x_5);
x_14 = lean_array_push(x_13, x_8);
x_15 = lean_array_push(x_14, x_10);
x_16 = lean_unsigned_to_nat(4u);
x_17 = lean_mk_string_unchecked("null", 4, 4);
x_18 = l_Lean_Name_mkStr1(x_17);
x_19 = lean_box(2);
x_20 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_15);
x_21 = l_Lean_Syntax_setArg(x_1, x_16, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_unsigned_to_nat(4u);
x_23 = l_Array_empty(lean_box(0));
x_24 = lean_mk_string_unchecked("null", 4, 4);
x_25 = l_Lean_Name_mkStr1(x_24);
x_26 = lean_box(2);
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_27, 2, x_23);
x_28 = l_Lean_Syntax_setArg(x_1, x_22, x_27);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_setSimpParams___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_setSimpParams(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_simpOnlyBuiltins() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_mk_string_unchecked("eq_self", 7, 7);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_mk_string_unchecked("iff_self", 8, 8);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_mkSimpContext_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_4, x_3);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_10);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_array_uget(x_2, x_4);
lean_inc(x_20);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lean_Meta_SimpTheoremsArray_isErased(x_5, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_inc(x_6);
x_23 = l_Lean_FVarId_getDecl___redArg(x_20, x_6, x_8, x_9, x_10);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_LocalDecl_toExpr(x_24);
x_27 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_28 = l_Lean_Meta_SimpTheoremsArray_addTheorem(x_5, x_21, x_26, x_27, x_6, x_7, x_8, x_9, x_25);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_11 = x_29;
x_12 = x_30;
goto block_17;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_28;
}
}
else
{
uint8_t x_31; 
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_dec(x_21);
lean_dec(x_20);
x_11 = x_5;
x_12 = x_10;
goto block_17;
}
}
block_17:
{
lean_object* x_13; size_t x_14; size_t x_15; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_usize_of_nat(x_13);
x_15 = lean_usize_add(x_4, x_14);
x_4 = x_15;
x_5 = x_11;
x_10 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_mkSimpContext_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_mkSimpContext_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Elab_Tactic_mkSimpContext_spec__1___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = lean_unsigned_to_nat(1000u);
x_14 = lean_unbox(x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_Lean_Meta_SimpTheorems_addConst(x_2, x_10, x_1, x_14, x_13, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_2 = x_16;
x_3 = x_11;
x_8 = x_17;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Elab_Tactic_mkSimpContext_spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_foldlM___at___Lean_Elab_Tactic_mkSimpContext_spec__1___redArg(x_1, x_2, x_3, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpContext___lam__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_16 = lean_unsigned_to_nat(2u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
lean_inc(x_9);
x_18 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_mkDischargeWrapper___redArg(x_17, x_9, x_10, x_13, x_14, x_15);
lean_dec(x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_99 = lean_unsigned_to_nat(3u);
x_100 = l_Lean_Syntax_getArg(x_1, x_99);
x_101 = l_Lean_Syntax_isNone(x_100);
lean_dec(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; 
lean_dec(x_5);
x_102 = lean_box(1);
x_103 = l_Lean_Meta_DiscrTree_empty(lean_box(0));
x_104 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_mkSimpExt_spec__0(lean_box(0));
x_105 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_Match_initFn____x40_Lean_Meta_Match_MatchEqsExt___hyg_181__spec__0(lean_box(0));
x_106 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_107 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_107, 0, x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc_n(x_103, 2);
x_108 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_108, 0, x_103);
lean_ctor_set(x_108, 1, x_103);
lean_ctor_set(x_108, 2, x_104);
lean_ctor_set(x_108, 3, x_105);
lean_ctor_set(x_108, 4, x_104);
lean_ctor_set(x_108, 5, x_107);
x_109 = lean_mk_string_unchecked("eq_self", 7, 7);
x_110 = l_Lean_Name_mkStr1(x_109);
x_111 = lean_mk_string_unchecked("iff_self", 8, 8);
x_112 = l_Lean_Name_mkStr1(x_111);
x_113 = lean_box(0);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_110);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_unbox(x_102);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_117 = l_List_foldlM___at___Lean_Elab_Tactic_mkSimpContext_spec__1___redArg(x_116, x_108, x_115, x_11, x_12, x_13, x_14, x_20);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
lean_inc(x_105);
lean_inc(x_103);
x_120 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_120, 0, x_103);
lean_ctor_set(x_120, 1, x_103);
lean_ctor_set(x_120, 2, x_105);
lean_ctor_set(x_120, 3, x_105);
x_29 = x_118;
x_30 = x_120;
x_31 = x_7;
x_32 = x_8;
x_33 = x_9;
x_34 = x_10;
x_35 = x_11;
x_36 = x_12;
x_37 = x_13;
x_38 = x_14;
x_39 = x_119;
goto block_98;
}
else
{
uint8_t x_121; 
lean_dec(x_105);
lean_dec(x_103);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_121 = !lean_is_exclusive(x_117);
if (x_121 == 0)
{
return x_117;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_117, 0);
x_123 = lean_ctor_get(x_117, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_117);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
else
{
lean_object* x_125; 
lean_inc(x_14);
lean_inc(x_13);
x_125 = lean_apply_3(x_5, x_13, x_14, x_20);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = l_Lean_Meta_Simp_getSimprocs(x_13, x_14, x_127);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_29 = x_126;
x_30 = x_129;
x_31 = x_7;
x_32 = x_8;
x_33 = x_9;
x_34 = x_10;
x_35 = x_11;
x_36 = x_12;
x_37 = x_13;
x_38 = x_14;
x_39 = x_130;
goto block_98;
}
else
{
uint8_t x_131; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_131 = !lean_is_exclusive(x_125);
if (x_131 == 0)
{
return x_125;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_125, 0);
x_133 = lean_ctor_get(x_125, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_125);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
block_28:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_19);
if (lean_is_scalar(x_21)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_21;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_22);
return x_27;
}
block_98:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = l_Lean_Meta_getSimpCongrTheorems(x_37, x_38, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_unsigned_to_nat(1u);
x_44 = l_Lean_Syntax_getArg(x_1, x_43);
lean_inc(x_38);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
x_45 = l_Lean_Elab_Tactic_elabSimpConfig___redArg(x_44, x_2, x_31, x_33, x_34, x_35, x_36, x_37, x_38, x_42);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_mk_empty_array_with_capacity(x_43);
lean_inc(x_48);
x_49 = lean_array_push(x_48, x_29);
x_50 = l_Lean_Meta_Simp_mkContext(x_46, x_49, x_41, x_35, x_36, x_37, x_38, x_47);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_unsigned_to_nat(4u);
x_54 = l_Lean_Syntax_getArg(x_1, x_53);
x_55 = lean_array_push(x_48, x_30);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
x_56 = l_Lean_Elab_Tactic_elabSimpArgs(x_54, x_51, x_55, x_3, x_2, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_52);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get_uint8(x_57, sizeof(void*)*2);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_22 = x_59;
x_23 = x_57;
goto block_28;
}
else
{
if (x_4 == 0)
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_21);
x_60 = lean_ctor_get(x_56, 1);
lean_inc(x_60);
lean_dec(x_56);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
x_61 = l_Lean_Meta_getPropHyps(x_35, x_36, x_37, x_38, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; size_t x_66; lean_object* x_67; size_t x_68; lean_object* x_69; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_ctor_get(x_57, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_64, 5);
lean_inc(x_65);
x_66 = lean_array_size(x_62);
x_67 = lean_unsigned_to_nat(0u);
x_68 = lean_usize_of_nat(x_67);
x_69 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_mkSimpContext_spec__0___redArg(x_64, x_62, x_66, x_68, x_65, x_35, x_36, x_37, x_38, x_63);
lean_dec(x_62);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_69, 0);
x_72 = lean_ctor_get(x_57, 1);
lean_inc(x_72);
lean_dec(x_57);
x_73 = l_Lean_Meta_Simp_Context_setSimpTheorems(x_64, x_71);
lean_dec(x_64);
x_74 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
lean_ctor_set(x_74, 2, x_19);
lean_ctor_set(x_69, 0, x_74);
return x_69;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_69, 0);
x_76 = lean_ctor_get(x_69, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_69);
x_77 = lean_ctor_get(x_57, 1);
lean_inc(x_77);
lean_dec(x_57);
x_78 = l_Lean_Meta_Simp_Context_setSimpTheorems(x_64, x_75);
lean_dec(x_64);
x_79 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
lean_ctor_set(x_79, 2, x_19);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_76);
return x_80;
}
}
else
{
uint8_t x_81; 
lean_dec(x_64);
lean_dec(x_57);
lean_dec(x_19);
x_81 = !lean_is_exclusive(x_69);
if (x_81 == 0)
{
return x_69;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_69, 0);
x_83 = lean_ctor_get(x_69, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_69);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_57);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_19);
x_85 = !lean_is_exclusive(x_61);
if (x_85 == 0)
{
return x_61;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_61, 0);
x_87 = lean_ctor_get(x_61, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_61);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
lean_object* x_89; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
x_89 = lean_ctor_get(x_56, 1);
lean_inc(x_89);
lean_dec(x_56);
x_22 = x_89;
x_23 = x_57;
goto block_28;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_21);
lean_dec(x_19);
x_90 = !lean_is_exclusive(x_56);
if (x_90 == 0)
{
return x_56;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_56, 0);
x_92 = lean_ctor_get(x_56, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_56);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_41);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_21);
lean_dec(x_19);
x_94 = !lean_is_exclusive(x_45);
if (x_94 == 0)
{
return x_45;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_45, 0);
x_96 = lean_ctor_get(x_45, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_45);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpContext(lean_object* x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_unsigned_to_nat(2u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = l_Lean_Syntax_isNone(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; uint8_t x_20; 
x_18 = lean_box(1);
x_19 = lean_unbox(x_18);
x_20 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_beqSimpKind____x40_Lean_Elab_Tactic_Simp___hyg_1730_(x_3, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; uint8_t x_23; 
x_21 = lean_box(2);
x_22 = lean_unbox(x_21);
x_23 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_beqSimpKind____x40_Lean_Elab_Tactic_Simp___hyg_1730_(x_3, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
x_25 = l_Lean_Elab_Tactic_mkSimpContext___lam__0(x_1, x_3, x_2, x_4, x_5, x_24, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_26 = lean_mk_string_unchecked("'dsimp' tactic does not support 'discharger' option", 51, 51);
x_27 = l_Lean_stringToMessageData(x_26);
lean_dec(x_26);
x_28 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_27, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
return x_28;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_33 = lean_mk_string_unchecked("'simp_all' tactic does not support 'discharger' option", 54, 54);
x_34 = l_Lean_stringToMessageData(x_33);
lean_dec(x_33);
x_35 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_34, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
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
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_box(0);
x_41 = l_Lean_Elab_Tactic_mkSimpContext___lam__0(x_1, x_3, x_2, x_4, x_5, x_40, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_mkSimpContext_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_mkSimpContext_spec__0___redArg(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_mkSimpContext_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_mkSimpContext_spec__0(x_1, x_2, x_15, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Elab_Tactic_mkSimpContext_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_List_foldlM___at___Lean_Elab_Tactic_mkSimpContext_spec__1___redArg(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Elab_Tactic_mkSimpContext_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = l_List_foldlM___at___Lean_Elab_Tactic_mkSimpContext_spec__1(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpContext___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_16 = lean_unbox(x_2);
lean_dec(x_2);
x_17 = lean_unbox(x_3);
lean_dec(x_3);
x_18 = lean_unbox(x_4);
lean_dec(x_4);
x_19 = l_Lean_Elab_Tactic_mkSimpContext___lam__0(x_1, x_16, x_17, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_6);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = lean_unbox(x_3);
lean_dec(x_3);
x_17 = lean_unbox(x_4);
lean_dec(x_4);
x_18 = l_Lean_Elab_Tactic_mkSimpContext(x_1, x_15, x_16, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_7019_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_2 = lean_mk_string_unchecked("tactic", 6, 6);
x_3 = lean_mk_string_unchecked("simp", 4, 4);
x_4 = lean_mk_string_unchecked("trace", 5, 5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_box(0);
x_7 = lean_mk_string_unchecked("", 0, 0);
x_8 = lean_mk_string_unchecked("When tracing is enabled, calls to `simp` or `dsimp` will print an equivalent `simp only` call.", 94, 94);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
x_10 = lean_mk_string_unchecked("Lean", 4, 4);
x_11 = lean_mk_string_unchecked("Elab", 4, 4);
x_12 = lean_mk_string_unchecked("Tactic", 6, 6);
x_13 = l_Lean_Name_mkStr6(x_10, x_11, x_12, x_2, x_3, x_4);
x_14 = l_Lean_Option_register___at___Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6__spec__0(x_5, x_9, x_13, x_1);
lean_dec(x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___Lean_resolveLocalName_loop___at___Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_2, 6);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 7);
lean_inc(x_10);
lean_dec(x_2);
x_11 = l_Lean_ResolveName_resolveGlobalName(x_8, x_9, x_10, x_1);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_2, 6);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 7);
lean_inc(x_16);
lean_dec(x_2);
x_17 = l_Lean_ResolveName_resolveGlobalName(x_14, x_15, x_16, x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___Lean_resolveLocalName_loop___at___Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_resolveGlobalName___at___Lean_resolveLocalName_loop___at___Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0_spec__0_spec__0___redArg(x_1, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName_loop___at___Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_2);
x_14 = l_Lean_resolveLocalName_loop___at___Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0_spec__0(x_3, x_4, x_5, x_13, x_6, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName_loop___at___Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_ctor_get(x_1, 3);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_3);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_12);
lean_ctor_set(x_14, 3, x_13);
if (x_5 == 0)
{
x_15 = x_5;
goto block_49;
}
else
{
uint8_t x_50; 
x_50 = l_List_isEmpty___redArg(x_4);
if (x_50 == 0)
{
x_15 = x_5;
goto block_49;
}
else
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_box(0);
x_52 = lean_unbox(x_51);
x_15 = x_52;
goto block_49;
}
}
block_49:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(x_15);
lean_inc(x_2);
lean_inc(x_14);
x_17 = lean_apply_2(x_2, x_14, x_16);
if (lean_obj_tag(x_17) == 0)
{
if (lean_obj_tag(x_3) == 1)
{
if (x_5 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
lean_dec(x_3);
x_20 = l_Lean_MacroScopesView_review(x_14);
lean_inc(x_8);
x_21 = l_Lean_resolveGlobalName___at___Lean_resolveLocalName_loop___at___Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0_spec__0_spec__0___redArg(x_20, x_8, x_9, x_10);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_box(0);
x_25 = l_List_filterTR_loop___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__0(x_22, x_24);
x_26 = l_List_isEmpty___redArg(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_27 = lean_box(1);
x_28 = lean_box(0);
x_29 = lean_unbox(x_27);
x_30 = l_Lean_resolveLocalName_loop___at___Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0_spec__0___lam__0(x_19, x_4, x_1, x_2, x_18, x_29, x_28, x_6, x_7, x_8, x_9, x_23);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_box(0);
x_32 = l_Lean_resolveLocalName_loop___at___Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0_spec__0___lam__0(x_19, x_4, x_1, x_2, x_18, x_5, x_31, x_6, x_7, x_8, x_9, x_23);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_14);
x_33 = lean_ctor_get(x_3, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_3, 1);
lean_inc(x_34);
lean_dec(x_3);
x_35 = lean_box(0);
x_36 = l_Lean_resolveLocalName_loop___at___Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0_spec__0___lam__0(x_34, x_4, x_1, x_2, x_33, x_5, x_35, x_6, x_7, x_8, x_9, x_10);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_10);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_17);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_17, 0);
x_41 = l_Lean_LocalDecl_toExpr(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_4);
lean_ctor_set(x_17, 0, x_42);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_17);
lean_ctor_set(x_43, 1, x_10);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_17, 0);
lean_inc(x_44);
lean_dec(x_17);
x_45 = l_Lean_LocalDecl_toExpr(x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_4);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_10);
return x_48;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_4);
x_6 = l_Lean_MacroScopesView_review(x_4);
x_7 = lean_ctor_get(x_1, 1);
x_8 = l_Lean_PersistentArray_findSomeRevM_x3f___at___Lean_resolveLocalName___at___Lean_Elab_Term_isLocalIdent_x3f_spec__0_spec__1(x_6, x_5, x_2, x_3, x_4, x_7);
if (lean_obj_tag(x_8) == 0)
{
if (x_5 == 0)
{
lean_object* x_9; 
x_9 = l_Lean_PersistentArray_findSomeRevM_x3f___at___Lean_resolveLocalName___at___Lean_Elab_Term_isLocalIdent_x3f_spec__0_spec__5(x_8, x_6, x_7);
lean_dec(x_6);
return x_9;
}
else
{
lean_dec(x_6);
return x_8;
}
}
else
{
lean_dec(x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0___lam__0___boxed), 5, 3);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_4);
x_9 = l_Lean_extractMacroScopes(x_1);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_box(0);
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
x_14 = l_Lean_resolveLocalName_loop___at___Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0_spec__0(x_9, x_8, x_10, x_11, x_13, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_unresolveNameGlobal_unresolveNameCore___at___Lean_unresolveNameGlobal___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__3_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_dec(x_4);
x_14 = l_Lean_Name_appendCore(x_11, x_13);
lean_inc(x_7);
lean_inc(x_14);
x_15 = l_Lean_resolveGlobalName___at___Lean_resolveLocalName_loop___at___Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0_spec__0_spec__0___redArg(x_14, x_7, x_8, x_9);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
x_19 = lean_box(0);
if (lean_obj_tag(x_16) == 0)
{
goto block_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_dec(x_16);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_dec(x_18);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_ctor_get(x_23, 1);
lean_dec(x_27);
x_28 = lean_name_eq(x_26, x_1);
lean_dec(x_26);
if (x_28 == 0)
{
lean_ctor_set(x_23, 1, x_14);
lean_ctor_set(x_23, 0, x_19);
x_3 = x_12;
x_4 = x_23;
x_9 = x_17;
goto _start;
}
else
{
lean_object* x_30; 
lean_inc(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_14);
x_30 = lean_apply_6(x_2, x_14, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
lean_ctor_set(x_23, 1, x_14);
lean_ctor_set(x_23, 0, x_19);
x_3 = x_12;
x_4 = x_23;
x_9 = x_33;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
lean_dec(x_36);
lean_inc(x_14);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_14);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_23, 1, x_14);
lean_ctor_set(x_23, 0, x_38);
lean_ctor_set(x_30, 0, x_23);
return x_30;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_30, 1);
lean_inc(x_39);
lean_dec(x_30);
lean_inc(x_14);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_14);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_23, 1, x_14);
lean_ctor_set(x_23, 0, x_41);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_23);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_free_object(x_23);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_30);
if (x_43 == 0)
{
return x_30;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_30, 0);
x_45 = lean_ctor_get(x_30, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_30);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_23, 0);
lean_inc(x_47);
lean_dec(x_23);
x_48 = lean_name_eq(x_47, x_1);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_19);
lean_ctor_set(x_49, 1, x_14);
x_3 = x_12;
x_4 = x_49;
x_9 = x_17;
goto _start;
}
else
{
lean_object* x_51; 
lean_inc(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_14);
x_51 = lean_apply_6(x_2, x_14, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_unbox(x_52);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_19);
lean_ctor_set(x_55, 1, x_14);
x_3 = x_12;
x_4 = x_55;
x_9 = x_54;
goto _start;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_57 = lean_ctor_get(x_51, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_58 = x_51;
} else {
 lean_dec_ref(x_51);
 x_58 = lean_box(0);
}
lean_inc(x_14);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_14);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_14);
if (lean_is_scalar(x_58)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_58;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_57);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_63 = lean_ctor_get(x_51, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_51, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_65 = x_51;
} else {
 lean_dec_ref(x_51);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
}
else
{
lean_dec(x_24);
lean_dec(x_23);
goto block_22;
}
}
block_22:
{
lean_object* x_20; 
if (lean_is_scalar(x_18)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_18;
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
x_3 = x_12;
x_4 = x_20;
x_9 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_unresolveNameGlobal_unresolveNameCore___at___Lean_unresolveNameGlobal___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__3_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_x27_loop___at___Lean_unresolveNameGlobal_unresolveNameCore___at___Lean_unresolveNameGlobal___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__3_spec__3_spec__3___redArg(x_1, x_2, x_4, x_5, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___at___Lean_unresolveNameGlobal___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = l_Lean_Name_hasMacroScopes(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_Name_componentsRev(x_3);
x_11 = lean_box(0);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_List_forIn_x27_loop___at___Lean_unresolveNameGlobal_unresolveNameCore___at___Lean_unresolveNameGlobal___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__3_spec__3_spec__3___redArg(x_1, x_2, x_10, x_13, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_14, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_16, 0);
lean_inc(x_25);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_25);
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_ctor_get(x_16, 0);
lean_inc(x_27);
lean_dec(x_16);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_14);
if (x_29 == 0)
{
return x_14;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_14, 0);
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_14);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_8);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_unresolveNameGlobal___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__3_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
x_14 = lean_array_uget(x_3, x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_15 = l_Lean_unresolveNameGlobal_unresolveNameCore___at___Lean_unresolveNameGlobal___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__3_spec__3(x_1, x_2, x_14, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_box(0);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
lean_free_object(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_usize_of_nat(x_22);
x_24 = lean_usize_add(x_5, x_23);
x_5 = x_24;
x_6 = x_21;
x_11 = x_18;
goto _start;
}
else
{
lean_object* x_26; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_17);
lean_ctor_set(x_26, 1, x_19);
lean_ctor_set(x_15, 0, x_26);
return x_15;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_15, 0);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_15);
x_29 = lean_box(0);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; 
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_usize_of_nat(x_32);
x_34 = lean_usize_add(x_5, x_33);
x_5 = x_34;
x_6 = x_31;
x_11 = x_28;
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_27);
lean_ctor_set(x_36, 1, x_29);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_28);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_15);
if (x_38 == 0)
{
return x_15;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_15, 0);
x_40 = lean_ctor_get(x_15, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_15);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__3___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; lean_object* x_17; size_t x_18; lean_object* x_19; 
x_10 = l_Lean_rootNamespace;
lean_inc(x_1);
x_11 = l_Lean_Name_append(x_10, x_1);
x_12 = lean_array_push(x_3, x_11);
x_13 = lean_box(0);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_array_size(x_12);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_usize_of_nat(x_17);
x_19 = l_Array_forIn_x27Unsafe_loop___at___Lean_unresolveNameGlobal___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__3_spec__5(x_1, x_2, x_12, x_16, x_18, x_15, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_19, 0);
lean_dec(x_23);
lean_ctor_set(x_19, 0, x_1);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_19, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_28);
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_dec(x_19);
x_30 = lean_ctor_get(x_21, 0);
lean_inc(x_30);
lean_dec(x_21);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_19);
if (x_32 == 0)
{
return x_19;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_19, 0);
x_34 = lean_ctor_get(x_19, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_19);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__3(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Name_hasMacroScopes(x_1);
if (x_10 == 0)
{
if (x_2 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_st_ref_get(x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_18 = lean_ctor_get(x_12, 0);
lean_inc(x_18);
lean_dec(x_12);
lean_inc(x_1);
x_19 = l_Lean_getRevAliases(x_18, x_1);
x_20 = lean_array_mk(x_19);
if (x_3 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_get_size(x_20);
x_23 = lean_mk_empty_array_with_capacity(x_21);
x_24 = lean_nat_dec_lt(x_21, x_22);
if (x_24 == 0)
{
lean_dec(x_22);
lean_dec(x_20);
x_14 = x_23;
goto block_17;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_22, x_22);
if (x_25 == 0)
{
lean_dec(x_22);
lean_dec(x_20);
x_14 = x_23;
goto block_17;
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; 
x_26 = lean_usize_of_nat(x_21);
x_27 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_28 = l_Array_foldlMUnsafe_fold___at___Lean_unresolveNameGlobal___at___Lean_PrettyPrinter_Delaborator_delabConst_spec__1_spec__5(x_1, x_20, x_26, x_27, x_23);
lean_dec(x_20);
x_14 = x_28;
goto block_17;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_box(0);
x_30 = l_Lean_unresolveNameGlobal___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__3___lam__0(x_1, x_4, x_20, x_29, x_5, x_6, x_7, x_8, x_13);
return x_30;
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Lean_unresolveNameGlobal___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__3___lam__0(x_1, x_4, x_14, x_15, x_5, x_6, x_7, x_8, x_13);
return x_16;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_inc(x_1);
x_31 = l_Lean_resolveGlobalName___at___Lean_resolveLocalName_loop___at___Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0_spec__0_spec__0___redArg(x_1, x_7, x_8, x_9);
lean_dec(x_8);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_34 = x_31;
} else {
 lean_dec_ref(x_31);
 x_34 = lean_box(0);
}
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_42; 
lean_dec(x_34);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_33);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_32, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_32, 1);
lean_inc(x_44);
lean_dec(x_32);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_45);
x_46 = lean_private_to_user_name(x_45);
if (lean_obj_tag(x_46) == 0)
{
x_35 = x_45;
goto block_41;
}
else
{
lean_object* x_47; 
lean_dec(x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec(x_46);
x_35 = x_47;
goto block_41;
}
}
else
{
uint8_t x_48; 
lean_dec(x_43);
lean_dec(x_34);
x_48 = !lean_is_exclusive(x_44);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_44, 1);
lean_dec(x_49);
x_50 = lean_ctor_get(x_44, 0);
lean_dec(x_50);
lean_ctor_set_tag(x_44, 0);
lean_ctor_set(x_44, 1, x_33);
lean_ctor_set(x_44, 0, x_1);
return x_44;
}
else
{
lean_object* x_51; 
lean_dec(x_44);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_33);
return x_51;
}
}
}
block_41:
{
uint8_t x_36; 
x_36 = lean_name_eq(x_35, x_1);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = l_Lean_rootNamespace;
x_38 = l_Lean_Name_append(x_37, x_1);
if (lean_is_scalar(x_34)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_34;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_33);
return x_39;
}
else
{
lean_object* x_40; 
if (lean_is_scalar(x_34)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_34;
}
lean_ctor_set(x_40, 0, x_1);
lean_ctor_set(x_40, 1, x_33);
return x_40;
}
}
}
}
else
{
lean_object* x_52; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_1);
lean_ctor_set(x_52, 1, x_9);
return x_52;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0(x_2, x_3, x_4, x_5, x_6, x_7);
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
x_12 = lean_box(1);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_box(1);
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
x_18 = lean_box(x_1);
lean_ctor_set(x_8, 0, x_18);
return x_8;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_dec(x_8);
x_20 = lean_box(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_box(0);
x_9 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0___lam__0___boxed), 7, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = lean_unbox(x_8);
x_11 = l_Lean_unresolveNameGlobal___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__3(x_1, x_2, x_10, x_9, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_mkSimpOnly_spec__8_spec__8___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_SourceInfo_fromRef(x_7, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_mkSimpOnly_spec__8_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_20; uint8_t x_21; 
x_20 = lean_mk_string_unchecked("simpAll", 7, 7);
x_21 = lean_usize_dec_lt(x_6, x_5);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_7);
lean_ctor_set(x_22, 1, x_12);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_23 = lean_mk_string_unchecked("Lean", 4, 4);
x_24 = lean_mk_string_unchecked("Parser", 6, 6);
x_25 = lean_mk_string_unchecked("Tactic", 6, 6);
x_26 = lean_array_uget(x_4, x_6);
x_27 = lean_ctor_get(x_7, 0);
lean_inc(x_27);
x_41 = lean_ctor_get(x_7, 1);
lean_inc(x_41);
lean_dec(x_7);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_291; uint8_t x_293; 
lean_dec(x_20);
x_54 = lean_ctor_get(x_26, 0);
lean_inc(x_54);
x_55 = lean_ctor_get_uint8(x_26, sizeof(void*)*1);
x_56 = lean_ctor_get_uint8(x_26, sizeof(void*)*1 + 1);
lean_dec(x_26);
lean_inc(x_54);
lean_inc(x_1);
x_293 = l_Lean_Environment_contains(x_1, x_54, x_21);
if (x_293 == 0)
{
x_291 = x_293;
goto block_292;
}
else
{
if (x_56 == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; uint8_t x_301; 
x_294 = lean_box(0);
x_295 = lean_mk_string_unchecked("eq_self", 7, 7);
x_296 = l_Lean_Name_mkStr1(x_295);
x_297 = lean_mk_string_unchecked("iff_self", 8, 8);
x_298 = l_Lean_Name_mkStr1(x_297);
x_299 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_294);
x_300 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_300, 0, x_296);
lean_ctor_set(x_300, 1, x_299);
x_301 = l_List_elem___at___Lean_Environment_realizeConst_spec__4(x_54, x_300);
lean_dec(x_300);
if (x_301 == 0)
{
x_291 = x_293;
goto block_292;
}
else
{
x_57 = x_56;
goto block_116;
}
}
else
{
goto block_290;
}
}
block_116:
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = l_Lean_Meta_Simp_isBuiltinSimproc(x_54, x_10, x_11, x_12);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_unbox(x_59);
lean_dec(x_59);
if (x_60 == 0)
{
uint8_t x_61; 
lean_dec(x_54);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
x_61 = !lean_is_exclusive(x_58);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_58, 1);
x_63 = lean_ctor_get(x_58, 0);
lean_dec(x_63);
lean_ctor_set(x_58, 1, x_41);
lean_ctor_set(x_58, 0, x_27);
x_13 = x_58;
x_14 = x_62;
goto block_19;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
lean_dec(x_58);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_27);
lean_ctor_set(x_65, 1, x_41);
x_13 = x_65;
x_14 = x_64;
goto block_19;
}
}
else
{
if (x_55 == 0)
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_58, 1);
lean_inc(x_66);
lean_dec(x_58);
x_67 = lean_st_ref_get(x_11, x_66);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_69 = lean_ctor_get(x_67, 1);
x_70 = lean_ctor_get(x_67, 0);
lean_dec(x_70);
x_71 = lean_ctor_get(x_10, 5);
lean_inc(x_71);
x_72 = l_Lean_SourceInfo_fromRef(x_71, x_55);
lean_dec(x_71);
x_73 = lean_mk_string_unchecked("simpLemma", 9, 9);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_74 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_73);
x_75 = lean_mk_string_unchecked("null", 4, 4);
x_76 = l_Lean_Name_mkStr1(x_75);
x_77 = lean_mk_string_unchecked("simpPre", 7, 7);
x_78 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_77);
x_79 = lean_mk_string_unchecked("↓", 3, 1);
lean_inc(x_72);
lean_ctor_set_tag(x_67, 2);
lean_ctor_set(x_67, 1, x_79);
lean_ctor_set(x_67, 0, x_72);
lean_inc(x_72);
x_80 = l_Lean_Syntax_node1(x_72, x_78, x_67);
lean_inc(x_76);
lean_inc(x_72);
x_81 = l_Lean_Syntax_node1(x_72, x_76, x_80);
x_82 = l_Array_mkArray0(lean_box(0));
lean_inc(x_72);
x_83 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_83, 0, x_72);
lean_ctor_set(x_83, 1, x_76);
lean_ctor_set(x_83, 2, x_82);
x_84 = lean_mk_syntax_ident(x_54);
x_85 = l_Lean_Syntax_node3(x_72, x_74, x_81, x_83, x_84);
x_48 = x_27;
x_49 = x_85;
x_50 = x_69;
goto block_53;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_86 = lean_ctor_get(x_67, 1);
lean_inc(x_86);
lean_dec(x_67);
x_87 = lean_ctor_get(x_10, 5);
lean_inc(x_87);
x_88 = l_Lean_SourceInfo_fromRef(x_87, x_55);
lean_dec(x_87);
x_89 = lean_mk_string_unchecked("simpLemma", 9, 9);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_90 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_89);
x_91 = lean_mk_string_unchecked("null", 4, 4);
x_92 = l_Lean_Name_mkStr1(x_91);
x_93 = lean_mk_string_unchecked("simpPre", 7, 7);
x_94 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_93);
x_95 = lean_mk_string_unchecked("↓", 3, 1);
lean_inc(x_88);
x_96 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_96, 0, x_88);
lean_ctor_set(x_96, 1, x_95);
lean_inc(x_88);
x_97 = l_Lean_Syntax_node1(x_88, x_94, x_96);
lean_inc(x_92);
lean_inc(x_88);
x_98 = l_Lean_Syntax_node1(x_88, x_92, x_97);
x_99 = l_Array_mkArray0(lean_box(0));
lean_inc(x_88);
x_100 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_100, 0, x_88);
lean_ctor_set(x_100, 1, x_92);
lean_ctor_set(x_100, 2, x_99);
x_101 = lean_mk_syntax_ident(x_54);
x_102 = l_Lean_Syntax_node3(x_88, x_90, x_98, x_100, x_101);
x_48 = x_27;
x_49 = x_102;
x_50 = x_86;
goto block_53;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_103 = lean_ctor_get(x_58, 1);
lean_inc(x_103);
lean_dec(x_58);
x_104 = lean_st_ref_get(x_11, x_103);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
x_106 = lean_ctor_get(x_10, 5);
lean_inc(x_106);
x_107 = l_Lean_SourceInfo_fromRef(x_106, x_57);
lean_dec(x_106);
x_108 = lean_mk_string_unchecked("simpLemma", 9, 9);
x_109 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_108);
x_110 = lean_mk_string_unchecked("null", 4, 4);
x_111 = l_Lean_Name_mkStr1(x_110);
x_112 = l_Array_mkArray0(lean_box(0));
lean_inc(x_107);
x_113 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_113, 0, x_107);
lean_ctor_set(x_113, 1, x_111);
lean_ctor_set(x_113, 2, x_112);
x_114 = lean_mk_syntax_ident(x_54);
lean_inc(x_113);
x_115 = l_Lean_Syntax_node3(x_107, x_109, x_113, x_113, x_114);
x_48 = x_27;
x_49 = x_115;
x_50 = x_105;
goto block_53;
}
}
}
block_290:
{
uint8_t x_117; 
lean_inc(x_54);
lean_inc(x_1);
x_117 = l_Lean_Meta_Match_isMatchEqnTheorem(x_1, x_54);
if (x_117 == 0)
{
lean_object* x_118; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_118 = l_Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0(x_54, x_117, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_st_ref_get(x_11, x_120);
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
lean_dec(x_121);
x_123 = lean_mk_syntax_ident(x_119);
if (x_55 == 0)
{
if (x_56 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_124 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_mkSimpOnly_spec__8_spec__8___lam__0(x_117, x_8, x_9, x_10, x_11, x_122);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_127 = lean_st_ref_get(x_11, x_126);
x_128 = !lean_is_exclusive(x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_129 = lean_ctor_get(x_127, 1);
x_130 = lean_ctor_get(x_127, 0);
lean_dec(x_130);
x_131 = lean_mk_string_unchecked("simpLemma", 9, 9);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_132 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_131);
x_133 = lean_mk_string_unchecked("null", 4, 4);
x_134 = l_Lean_Name_mkStr1(x_133);
x_135 = lean_mk_string_unchecked("simpPre", 7, 7);
x_136 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_135);
x_137 = lean_mk_string_unchecked("↓", 3, 1);
lean_inc(x_125);
lean_ctor_set_tag(x_127, 2);
lean_ctor_set(x_127, 1, x_137);
lean_ctor_set(x_127, 0, x_125);
lean_inc(x_125);
x_138 = l_Lean_Syntax_node1(x_125, x_136, x_127);
lean_inc(x_134);
lean_inc(x_125);
x_139 = l_Lean_Syntax_node1(x_125, x_134, x_138);
x_140 = l_Array_mkArray0(lean_box(0));
lean_inc(x_125);
x_141 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_141, 0, x_125);
lean_ctor_set(x_141, 1, x_134);
lean_ctor_set(x_141, 2, x_140);
x_142 = l_Lean_Syntax_node3(x_125, x_132, x_139, x_141, x_123);
x_42 = x_27;
x_43 = x_142;
x_44 = x_129;
goto block_47;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_143 = lean_ctor_get(x_127, 1);
lean_inc(x_143);
lean_dec(x_127);
x_144 = lean_mk_string_unchecked("simpLemma", 9, 9);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_145 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_144);
x_146 = lean_mk_string_unchecked("null", 4, 4);
x_147 = l_Lean_Name_mkStr1(x_146);
x_148 = lean_mk_string_unchecked("simpPre", 7, 7);
x_149 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_148);
x_150 = lean_mk_string_unchecked("↓", 3, 1);
lean_inc(x_125);
x_151 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_151, 0, x_125);
lean_ctor_set(x_151, 1, x_150);
lean_inc(x_125);
x_152 = l_Lean_Syntax_node1(x_125, x_149, x_151);
lean_inc(x_147);
lean_inc(x_125);
x_153 = l_Lean_Syntax_node1(x_125, x_147, x_152);
x_154 = l_Array_mkArray0(lean_box(0));
lean_inc(x_125);
x_155 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_155, 0, x_125);
lean_ctor_set(x_155, 1, x_147);
lean_ctor_set(x_155, 2, x_154);
x_156 = l_Lean_Syntax_node3(x_125, x_145, x_153, x_155, x_123);
x_42 = x_27;
x_43 = x_156;
x_44 = x_143;
goto block_47;
}
}
else
{
lean_object* x_157; uint8_t x_158; 
x_157 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_mkSimpOnly_spec__8_spec__8___lam__0(x_117, x_8, x_9, x_10, x_11, x_122);
x_158 = !lean_is_exclusive(x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_159 = lean_ctor_get(x_157, 0);
x_160 = lean_ctor_get(x_157, 1);
x_161 = lean_st_ref_get(x_11, x_160);
x_162 = !lean_is_exclusive(x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_163 = lean_ctor_get(x_161, 1);
x_164 = lean_ctor_get(x_161, 0);
lean_dec(x_164);
x_165 = lean_mk_string_unchecked("simpLemma", 9, 9);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_166 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_165);
x_167 = lean_mk_string_unchecked("null", 4, 4);
x_168 = l_Lean_Name_mkStr1(x_167);
x_169 = lean_mk_string_unchecked("simpPre", 7, 7);
x_170 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_169);
x_171 = lean_mk_string_unchecked("↓", 3, 1);
lean_inc(x_159);
lean_ctor_set_tag(x_161, 2);
lean_ctor_set(x_161, 1, x_171);
lean_ctor_set(x_161, 0, x_159);
lean_inc(x_159);
x_172 = l_Lean_Syntax_node1(x_159, x_170, x_161);
lean_inc(x_168);
lean_inc(x_159);
x_173 = l_Lean_Syntax_node1(x_159, x_168, x_172);
x_174 = lean_mk_string_unchecked("patternIgnore", 13, 13);
x_175 = l_Lean_Name_mkStr1(x_174);
x_176 = lean_mk_string_unchecked("token", 5, 5);
x_177 = lean_mk_string_unchecked("← ", 4, 2);
x_178 = l_Lean_Name_mkStr2(x_176, x_177);
x_179 = lean_mk_string_unchecked("←", 3, 1);
lean_inc(x_159);
lean_ctor_set_tag(x_157, 2);
lean_ctor_set(x_157, 1, x_179);
lean_inc(x_159);
x_180 = l_Lean_Syntax_node1(x_159, x_178, x_157);
lean_inc(x_159);
x_181 = l_Lean_Syntax_node1(x_159, x_175, x_180);
lean_inc(x_159);
x_182 = l_Lean_Syntax_node1(x_159, x_168, x_181);
x_183 = l_Lean_Syntax_node3(x_159, x_166, x_173, x_182, x_123);
x_42 = x_27;
x_43 = x_183;
x_44 = x_163;
goto block_47;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_184 = lean_ctor_get(x_161, 1);
lean_inc(x_184);
lean_dec(x_161);
x_185 = lean_mk_string_unchecked("simpLemma", 9, 9);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_186 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_185);
x_187 = lean_mk_string_unchecked("null", 4, 4);
x_188 = l_Lean_Name_mkStr1(x_187);
x_189 = lean_mk_string_unchecked("simpPre", 7, 7);
x_190 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_189);
x_191 = lean_mk_string_unchecked("↓", 3, 1);
lean_inc(x_159);
x_192 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_192, 0, x_159);
lean_ctor_set(x_192, 1, x_191);
lean_inc(x_159);
x_193 = l_Lean_Syntax_node1(x_159, x_190, x_192);
lean_inc(x_188);
lean_inc(x_159);
x_194 = l_Lean_Syntax_node1(x_159, x_188, x_193);
x_195 = lean_mk_string_unchecked("patternIgnore", 13, 13);
x_196 = l_Lean_Name_mkStr1(x_195);
x_197 = lean_mk_string_unchecked("token", 5, 5);
x_198 = lean_mk_string_unchecked("← ", 4, 2);
x_199 = l_Lean_Name_mkStr2(x_197, x_198);
x_200 = lean_mk_string_unchecked("←", 3, 1);
lean_inc(x_159);
lean_ctor_set_tag(x_157, 2);
lean_ctor_set(x_157, 1, x_200);
lean_inc(x_159);
x_201 = l_Lean_Syntax_node1(x_159, x_199, x_157);
lean_inc(x_159);
x_202 = l_Lean_Syntax_node1(x_159, x_196, x_201);
lean_inc(x_159);
x_203 = l_Lean_Syntax_node1(x_159, x_188, x_202);
x_204 = l_Lean_Syntax_node3(x_159, x_186, x_194, x_203, x_123);
x_42 = x_27;
x_43 = x_204;
x_44 = x_184;
goto block_47;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_205 = lean_ctor_get(x_157, 0);
x_206 = lean_ctor_get(x_157, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_157);
x_207 = lean_st_ref_get(x_11, x_206);
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
x_210 = lean_mk_string_unchecked("simpLemma", 9, 9);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_211 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_210);
x_212 = lean_mk_string_unchecked("null", 4, 4);
x_213 = l_Lean_Name_mkStr1(x_212);
x_214 = lean_mk_string_unchecked("simpPre", 7, 7);
x_215 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_214);
x_216 = lean_mk_string_unchecked("↓", 3, 1);
lean_inc(x_205);
if (lean_is_scalar(x_209)) {
 x_217 = lean_alloc_ctor(2, 2, 0);
} else {
 x_217 = x_209;
 lean_ctor_set_tag(x_217, 2);
}
lean_ctor_set(x_217, 0, x_205);
lean_ctor_set(x_217, 1, x_216);
lean_inc(x_205);
x_218 = l_Lean_Syntax_node1(x_205, x_215, x_217);
lean_inc(x_213);
lean_inc(x_205);
x_219 = l_Lean_Syntax_node1(x_205, x_213, x_218);
x_220 = lean_mk_string_unchecked("patternIgnore", 13, 13);
x_221 = l_Lean_Name_mkStr1(x_220);
x_222 = lean_mk_string_unchecked("token", 5, 5);
x_223 = lean_mk_string_unchecked("← ", 4, 2);
x_224 = l_Lean_Name_mkStr2(x_222, x_223);
x_225 = lean_mk_string_unchecked("←", 3, 1);
lean_inc(x_205);
x_226 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_226, 0, x_205);
lean_ctor_set(x_226, 1, x_225);
lean_inc(x_205);
x_227 = l_Lean_Syntax_node1(x_205, x_224, x_226);
lean_inc(x_205);
x_228 = l_Lean_Syntax_node1(x_205, x_221, x_227);
lean_inc(x_205);
x_229 = l_Lean_Syntax_node1(x_205, x_213, x_228);
x_230 = l_Lean_Syntax_node3(x_205, x_211, x_219, x_229, x_123);
x_42 = x_27;
x_43 = x_230;
x_44 = x_208;
goto block_47;
}
}
}
else
{
if (x_56 == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_231 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_mkSimpOnly_spec__8_spec__8___lam__0(x_117, x_8, x_9, x_10, x_11, x_122);
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
lean_dec(x_231);
x_234 = lean_st_ref_get(x_11, x_233);
x_235 = lean_ctor_get(x_234, 1);
lean_inc(x_235);
lean_dec(x_234);
x_236 = lean_mk_string_unchecked("simpLemma", 9, 9);
x_237 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_236);
x_238 = lean_mk_string_unchecked("null", 4, 4);
x_239 = l_Lean_Name_mkStr1(x_238);
x_240 = l_Array_mkArray0(lean_box(0));
lean_inc(x_232);
x_241 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_241, 0, x_232);
lean_ctor_set(x_241, 1, x_239);
lean_ctor_set(x_241, 2, x_240);
lean_inc(x_241);
x_242 = l_Lean_Syntax_node3(x_232, x_237, x_241, x_241, x_123);
x_42 = x_27;
x_43 = x_242;
x_44 = x_235;
goto block_47;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; 
x_243 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_mkSimpOnly_spec__8_spec__8___lam__0(x_117, x_8, x_9, x_10, x_11, x_122);
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
lean_dec(x_243);
x_246 = lean_st_ref_get(x_11, x_245);
x_247 = !lean_is_exclusive(x_246);
if (x_247 == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_248 = lean_ctor_get(x_246, 1);
x_249 = lean_ctor_get(x_246, 0);
lean_dec(x_249);
x_250 = lean_mk_string_unchecked("simpLemma", 9, 9);
x_251 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_250);
x_252 = lean_mk_string_unchecked("null", 4, 4);
x_253 = l_Lean_Name_mkStr1(x_252);
x_254 = l_Array_mkArray0(lean_box(0));
lean_inc(x_253);
lean_inc(x_244);
x_255 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_255, 0, x_244);
lean_ctor_set(x_255, 1, x_253);
lean_ctor_set(x_255, 2, x_254);
x_256 = lean_mk_string_unchecked("patternIgnore", 13, 13);
x_257 = l_Lean_Name_mkStr1(x_256);
x_258 = lean_mk_string_unchecked("token", 5, 5);
x_259 = lean_mk_string_unchecked("← ", 4, 2);
x_260 = l_Lean_Name_mkStr2(x_258, x_259);
x_261 = lean_mk_string_unchecked("←", 3, 1);
lean_inc(x_244);
lean_ctor_set_tag(x_246, 2);
lean_ctor_set(x_246, 1, x_261);
lean_ctor_set(x_246, 0, x_244);
lean_inc(x_244);
x_262 = l_Lean_Syntax_node1(x_244, x_260, x_246);
lean_inc(x_244);
x_263 = l_Lean_Syntax_node1(x_244, x_257, x_262);
lean_inc(x_244);
x_264 = l_Lean_Syntax_node1(x_244, x_253, x_263);
x_265 = l_Lean_Syntax_node3(x_244, x_251, x_255, x_264, x_123);
x_42 = x_27;
x_43 = x_265;
x_44 = x_248;
goto block_47;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_266 = lean_ctor_get(x_246, 1);
lean_inc(x_266);
lean_dec(x_246);
x_267 = lean_mk_string_unchecked("simpLemma", 9, 9);
x_268 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_267);
x_269 = lean_mk_string_unchecked("null", 4, 4);
x_270 = l_Lean_Name_mkStr1(x_269);
x_271 = l_Array_mkArray0(lean_box(0));
lean_inc(x_270);
lean_inc(x_244);
x_272 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_272, 0, x_244);
lean_ctor_set(x_272, 1, x_270);
lean_ctor_set(x_272, 2, x_271);
x_273 = lean_mk_string_unchecked("patternIgnore", 13, 13);
x_274 = l_Lean_Name_mkStr1(x_273);
x_275 = lean_mk_string_unchecked("token", 5, 5);
x_276 = lean_mk_string_unchecked("← ", 4, 2);
x_277 = l_Lean_Name_mkStr2(x_275, x_276);
x_278 = lean_mk_string_unchecked("←", 3, 1);
lean_inc(x_244);
x_279 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_279, 0, x_244);
lean_ctor_set(x_279, 1, x_278);
lean_inc(x_244);
x_280 = l_Lean_Syntax_node1(x_244, x_277, x_279);
lean_inc(x_244);
x_281 = l_Lean_Syntax_node1(x_244, x_274, x_280);
lean_inc(x_244);
x_282 = l_Lean_Syntax_node1(x_244, x_270, x_281);
x_283 = l_Lean_Syntax_node3(x_244, x_268, x_272, x_282, x_123);
x_42 = x_27;
x_43 = x_283;
x_44 = x_266;
goto block_47;
}
}
}
}
else
{
uint8_t x_284; 
lean_dec(x_41);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_284 = !lean_is_exclusive(x_118);
if (x_284 == 0)
{
return x_118;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_285 = lean_ctor_get(x_118, 0);
x_286 = lean_ctor_get(x_118, 1);
lean_inc(x_286);
lean_inc(x_285);
lean_dec(x_118);
x_287 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_287, 0, x_285);
lean_ctor_set(x_287, 1, x_286);
return x_287;
}
}
}
else
{
lean_object* x_288; uint8_t x_289; 
x_288 = lean_box(0);
x_289 = lean_unbox(x_288);
x_57 = x_289;
goto block_116;
}
}
block_292:
{
if (x_291 == 0)
{
x_57 = x_291;
goto block_116;
}
else
{
goto block_290;
}
}
}
case 1:
{
lean_object* x_302; lean_object* x_303; 
x_302 = lean_ctor_get(x_26, 0);
lean_inc(x_302);
lean_dec(x_26);
lean_inc(x_2);
x_303 = lean_local_ctx_find(x_2, x_302);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_20);
x_304 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_304, 0, x_27);
lean_ctor_set(x_304, 1, x_41);
x_13 = x_304;
x_14 = x_12;
goto block_19;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_329; lean_object* x_330; uint8_t x_331; uint8_t x_334; lean_object* x_335; uint8_t x_336; lean_object* x_337; lean_object* x_338; uint8_t x_341; lean_object* x_342; lean_object* x_343; uint8_t x_344; uint8_t x_347; lean_object* x_348; lean_object* x_349; uint8_t x_352; lean_object* x_356; uint8_t x_357; 
x_305 = lean_ctor_get(x_303, 0);
lean_inc(x_305);
lean_dec(x_303);
x_356 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_20);
lean_inc(x_3);
x_357 = l_Lean_Syntax_isOfKind(x_3, x_356);
lean_dec(x_356);
if (x_357 == 0)
{
goto block_359;
}
else
{
uint8_t x_360; 
x_360 = l_Lean_LocalDecl_hasValue(x_305);
if (x_360 == 0)
{
goto block_359;
}
else
{
lean_object* x_361; uint8_t x_362; 
x_361 = lean_box(0);
x_362 = lean_unbox(x_361);
x_352 = x_362;
goto block_355;
}
}
block_310:
{
lean_object* x_309; 
x_309 = lean_ctor_get(x_305, 1);
lean_inc(x_309);
lean_dec(x_305);
x_33 = x_306;
x_34 = x_307;
x_35 = x_308;
x_36 = x_309;
goto block_40;
}
block_315:
{
lean_object* x_314; 
x_314 = lean_ctor_get(x_313, 1);
lean_inc(x_314);
lean_dec(x_313);
x_306 = x_311;
x_307 = x_312;
x_308 = x_314;
goto block_310;
}
block_328:
{
lean_object* x_319; 
x_319 = l_Lean_LocalContext_findFromUserName_x3f(x_2, x_318);
lean_dec(x_318);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_320 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
x_321 = lean_mk_string_unchecked("Option.get!", 11, 11);
x_322 = lean_unsigned_to_nat(21u);
x_323 = lean_unsigned_to_nat(14u);
x_324 = lean_mk_string_unchecked("value is none", 13, 13);
x_325 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_320, x_321, x_322, x_323, x_324);
lean_dec(x_324);
lean_dec(x_321);
lean_dec(x_320);
x_326 = l_panic___at___Lean_LocalDecl_setBinderInfo_spec__0(x_325);
x_311 = x_316;
x_312 = x_317;
x_313 = x_326;
goto block_315;
}
else
{
lean_object* x_327; 
x_327 = lean_ctor_get(x_319, 0);
lean_inc(x_327);
lean_dec(x_319);
x_311 = x_316;
x_312 = x_317;
x_313 = x_327;
goto block_315;
}
}
block_333:
{
if (x_331 == 0)
{
lean_dec(x_330);
lean_dec(x_329);
lean_dec(x_305);
goto block_32;
}
else
{
lean_object* x_332; 
x_332 = lean_ctor_get(x_305, 2);
lean_inc(x_332);
x_316 = x_329;
x_317 = x_330;
x_318 = x_332;
goto block_328;
}
}
block_340:
{
uint8_t x_339; 
x_339 = l_Lean_Name_hasMacroScopes(x_338);
lean_dec(x_338);
if (x_339 == 0)
{
x_329 = x_335;
x_330 = x_337;
x_331 = x_336;
goto block_333;
}
else
{
x_329 = x_335;
x_330 = x_337;
x_331 = x_334;
goto block_333;
}
}
block_346:
{
if (x_344 == 0)
{
lean_dec(x_343);
lean_dec(x_342);
lean_dec(x_305);
goto block_32;
}
else
{
lean_object* x_345; 
x_345 = lean_ctor_get(x_305, 2);
lean_inc(x_345);
x_334 = x_341;
x_335 = x_342;
x_336 = x_344;
x_337 = x_343;
x_338 = x_345;
goto block_340;
}
}
block_351:
{
uint8_t x_350; 
lean_inc(x_349);
x_350 = lean_is_inaccessible_user_name(x_349);
if (x_350 == 0)
{
x_341 = x_347;
x_342 = x_349;
x_343 = x_348;
x_344 = x_21;
goto block_346;
}
else
{
x_341 = x_347;
x_342 = x_349;
x_343 = x_348;
x_344 = x_347;
goto block_346;
}
}
block_355:
{
if (lean_obj_tag(x_41) == 0)
{
lean_dec(x_305);
x_28 = x_41;
goto block_30;
}
else
{
lean_object* x_353; lean_object* x_354; 
x_353 = lean_ctor_get(x_41, 0);
lean_inc(x_353);
lean_dec(x_41);
x_354 = lean_ctor_get(x_305, 2);
lean_inc(x_354);
x_347 = x_352;
x_348 = x_353;
x_349 = x_354;
goto block_351;
}
}
block_359:
{
if (x_357 == 0)
{
x_352 = x_357;
goto block_355;
}
else
{
lean_object* x_358; 
lean_dec(x_305);
x_358 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_358, 0, x_27);
lean_ctor_set(x_358, 1, x_41);
x_13 = x_358;
x_14 = x_12;
goto block_19;
}
}
}
}
case 2:
{
uint8_t x_363; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_20);
x_363 = !lean_is_exclusive(x_26);
if (x_363 == 0)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_364 = lean_ctor_get(x_26, 1);
x_365 = lean_ctor_get(x_26, 0);
lean_dec(x_365);
x_366 = lean_array_push(x_27, x_364);
lean_ctor_set_tag(x_26, 0);
lean_ctor_set(x_26, 1, x_41);
lean_ctor_set(x_26, 0, x_366);
x_13 = x_26;
x_14 = x_12;
goto block_19;
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_367 = lean_ctor_get(x_26, 1);
lean_inc(x_367);
lean_dec(x_26);
x_368 = lean_array_push(x_27, x_367);
x_369 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_369, 0, x_368);
lean_ctor_set(x_369, 1, x_41);
x_13 = x_369;
x_14 = x_12;
goto block_19;
}
}
default: 
{
lean_object* x_370; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_20);
x_370 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_370, 0, x_27);
lean_ctor_set(x_370, 1, x_41);
x_13 = x_370;
x_14 = x_12;
goto block_19;
}
}
block_30:
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_13 = x_29;
x_14 = x_12;
goto block_19;
}
block_32:
{
lean_object* x_31; 
x_31 = lean_box(0);
x_28 = x_31;
goto block_30;
}
block_40:
{
uint8_t x_37; 
x_37 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_35, x_36);
lean_dec(x_36);
lean_dec(x_35);
if (x_37 == 0)
{
lean_dec(x_34);
lean_dec(x_33);
goto block_32;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_array_push(x_34, x_33);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_28 = x_39;
goto block_30;
}
}
block_47:
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_array_push(x_42, x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_41);
x_13 = x_46;
x_14 = x_44;
goto block_19;
}
block_53:
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_array_push(x_48, x_49);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_41);
x_13 = x_52;
x_14 = x_50;
goto block_19;
}
}
block_19:
{
lean_object* x_15; size_t x_16; size_t x_17; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_add(x_6, x_16);
x_6 = x_17;
x_7 = x_13;
x_12 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_mkSimpOnly_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_20; uint8_t x_21; 
x_20 = lean_mk_string_unchecked("simpAll", 7, 7);
x_21 = lean_usize_dec_lt(x_6, x_5);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_7);
lean_ctor_set(x_22, 1, x_12);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_23 = lean_mk_string_unchecked("Lean", 4, 4);
x_24 = lean_mk_string_unchecked("Parser", 6, 6);
x_25 = lean_mk_string_unchecked("Tactic", 6, 6);
x_26 = lean_array_uget(x_4, x_6);
x_27 = lean_ctor_get(x_7, 0);
lean_inc(x_27);
x_41 = lean_ctor_get(x_7, 1);
lean_inc(x_41);
lean_dec(x_7);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_291; uint8_t x_293; 
lean_dec(x_20);
x_54 = lean_ctor_get(x_26, 0);
lean_inc(x_54);
x_55 = lean_ctor_get_uint8(x_26, sizeof(void*)*1);
x_56 = lean_ctor_get_uint8(x_26, sizeof(void*)*1 + 1);
lean_dec(x_26);
lean_inc(x_54);
lean_inc(x_1);
x_293 = l_Lean_Environment_contains(x_1, x_54, x_21);
if (x_293 == 0)
{
x_291 = x_293;
goto block_292;
}
else
{
if (x_56 == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; uint8_t x_301; 
x_294 = lean_box(0);
x_295 = lean_mk_string_unchecked("eq_self", 7, 7);
x_296 = l_Lean_Name_mkStr1(x_295);
x_297 = lean_mk_string_unchecked("iff_self", 8, 8);
x_298 = l_Lean_Name_mkStr1(x_297);
x_299 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_294);
x_300 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_300, 0, x_296);
lean_ctor_set(x_300, 1, x_299);
x_301 = l_List_elem___at___Lean_Environment_realizeConst_spec__4(x_54, x_300);
lean_dec(x_300);
if (x_301 == 0)
{
x_291 = x_293;
goto block_292;
}
else
{
x_57 = x_56;
goto block_116;
}
}
else
{
goto block_290;
}
}
block_116:
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = l_Lean_Meta_Simp_isBuiltinSimproc(x_54, x_10, x_11, x_12);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_unbox(x_59);
lean_dec(x_59);
if (x_60 == 0)
{
uint8_t x_61; 
lean_dec(x_54);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
x_61 = !lean_is_exclusive(x_58);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_58, 1);
x_63 = lean_ctor_get(x_58, 0);
lean_dec(x_63);
lean_ctor_set(x_58, 1, x_41);
lean_ctor_set(x_58, 0, x_27);
x_13 = x_58;
x_14 = x_62;
goto block_19;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
lean_dec(x_58);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_27);
lean_ctor_set(x_65, 1, x_41);
x_13 = x_65;
x_14 = x_64;
goto block_19;
}
}
else
{
if (x_55 == 0)
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_58, 1);
lean_inc(x_66);
lean_dec(x_58);
x_67 = lean_st_ref_get(x_11, x_66);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_69 = lean_ctor_get(x_67, 1);
x_70 = lean_ctor_get(x_67, 0);
lean_dec(x_70);
x_71 = lean_ctor_get(x_10, 5);
lean_inc(x_71);
x_72 = l_Lean_SourceInfo_fromRef(x_71, x_55);
lean_dec(x_71);
x_73 = lean_mk_string_unchecked("simpLemma", 9, 9);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_74 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_73);
x_75 = lean_mk_string_unchecked("null", 4, 4);
x_76 = l_Lean_Name_mkStr1(x_75);
x_77 = lean_mk_string_unchecked("simpPre", 7, 7);
x_78 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_77);
x_79 = lean_mk_string_unchecked("↓", 3, 1);
lean_inc(x_72);
lean_ctor_set_tag(x_67, 2);
lean_ctor_set(x_67, 1, x_79);
lean_ctor_set(x_67, 0, x_72);
lean_inc(x_72);
x_80 = l_Lean_Syntax_node1(x_72, x_78, x_67);
lean_inc(x_76);
lean_inc(x_72);
x_81 = l_Lean_Syntax_node1(x_72, x_76, x_80);
x_82 = l_Array_mkArray0(lean_box(0));
lean_inc(x_72);
x_83 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_83, 0, x_72);
lean_ctor_set(x_83, 1, x_76);
lean_ctor_set(x_83, 2, x_82);
x_84 = lean_mk_syntax_ident(x_54);
x_85 = l_Lean_Syntax_node3(x_72, x_74, x_81, x_83, x_84);
x_48 = x_27;
x_49 = x_85;
x_50 = x_69;
goto block_53;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_86 = lean_ctor_get(x_67, 1);
lean_inc(x_86);
lean_dec(x_67);
x_87 = lean_ctor_get(x_10, 5);
lean_inc(x_87);
x_88 = l_Lean_SourceInfo_fromRef(x_87, x_55);
lean_dec(x_87);
x_89 = lean_mk_string_unchecked("simpLemma", 9, 9);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_90 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_89);
x_91 = lean_mk_string_unchecked("null", 4, 4);
x_92 = l_Lean_Name_mkStr1(x_91);
x_93 = lean_mk_string_unchecked("simpPre", 7, 7);
x_94 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_93);
x_95 = lean_mk_string_unchecked("↓", 3, 1);
lean_inc(x_88);
x_96 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_96, 0, x_88);
lean_ctor_set(x_96, 1, x_95);
lean_inc(x_88);
x_97 = l_Lean_Syntax_node1(x_88, x_94, x_96);
lean_inc(x_92);
lean_inc(x_88);
x_98 = l_Lean_Syntax_node1(x_88, x_92, x_97);
x_99 = l_Array_mkArray0(lean_box(0));
lean_inc(x_88);
x_100 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_100, 0, x_88);
lean_ctor_set(x_100, 1, x_92);
lean_ctor_set(x_100, 2, x_99);
x_101 = lean_mk_syntax_ident(x_54);
x_102 = l_Lean_Syntax_node3(x_88, x_90, x_98, x_100, x_101);
x_48 = x_27;
x_49 = x_102;
x_50 = x_86;
goto block_53;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_103 = lean_ctor_get(x_58, 1);
lean_inc(x_103);
lean_dec(x_58);
x_104 = lean_st_ref_get(x_11, x_103);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
x_106 = lean_ctor_get(x_10, 5);
lean_inc(x_106);
x_107 = l_Lean_SourceInfo_fromRef(x_106, x_57);
lean_dec(x_106);
x_108 = lean_mk_string_unchecked("simpLemma", 9, 9);
x_109 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_108);
x_110 = lean_mk_string_unchecked("null", 4, 4);
x_111 = l_Lean_Name_mkStr1(x_110);
x_112 = l_Array_mkArray0(lean_box(0));
lean_inc(x_107);
x_113 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_113, 0, x_107);
lean_ctor_set(x_113, 1, x_111);
lean_ctor_set(x_113, 2, x_112);
x_114 = lean_mk_syntax_ident(x_54);
lean_inc(x_113);
x_115 = l_Lean_Syntax_node3(x_107, x_109, x_113, x_113, x_114);
x_48 = x_27;
x_49 = x_115;
x_50 = x_105;
goto block_53;
}
}
}
block_290:
{
uint8_t x_117; 
lean_inc(x_54);
lean_inc(x_1);
x_117 = l_Lean_Meta_Match_isMatchEqnTheorem(x_1, x_54);
if (x_117 == 0)
{
lean_object* x_118; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_118 = l_Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0(x_54, x_117, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_st_ref_get(x_11, x_120);
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
lean_dec(x_121);
x_123 = lean_mk_syntax_ident(x_119);
if (x_55 == 0)
{
if (x_56 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_124 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_mkSimpOnly_spec__8_spec__8___lam__0(x_117, x_8, x_9, x_10, x_11, x_122);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_127 = lean_st_ref_get(x_11, x_126);
x_128 = !lean_is_exclusive(x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_129 = lean_ctor_get(x_127, 1);
x_130 = lean_ctor_get(x_127, 0);
lean_dec(x_130);
x_131 = lean_mk_string_unchecked("simpLemma", 9, 9);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_132 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_131);
x_133 = lean_mk_string_unchecked("null", 4, 4);
x_134 = l_Lean_Name_mkStr1(x_133);
x_135 = lean_mk_string_unchecked("simpPre", 7, 7);
x_136 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_135);
x_137 = lean_mk_string_unchecked("↓", 3, 1);
lean_inc(x_125);
lean_ctor_set_tag(x_127, 2);
lean_ctor_set(x_127, 1, x_137);
lean_ctor_set(x_127, 0, x_125);
lean_inc(x_125);
x_138 = l_Lean_Syntax_node1(x_125, x_136, x_127);
lean_inc(x_134);
lean_inc(x_125);
x_139 = l_Lean_Syntax_node1(x_125, x_134, x_138);
x_140 = l_Array_mkArray0(lean_box(0));
lean_inc(x_125);
x_141 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_141, 0, x_125);
lean_ctor_set(x_141, 1, x_134);
lean_ctor_set(x_141, 2, x_140);
x_142 = l_Lean_Syntax_node3(x_125, x_132, x_139, x_141, x_123);
x_42 = x_27;
x_43 = x_142;
x_44 = x_129;
goto block_47;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_143 = lean_ctor_get(x_127, 1);
lean_inc(x_143);
lean_dec(x_127);
x_144 = lean_mk_string_unchecked("simpLemma", 9, 9);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_145 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_144);
x_146 = lean_mk_string_unchecked("null", 4, 4);
x_147 = l_Lean_Name_mkStr1(x_146);
x_148 = lean_mk_string_unchecked("simpPre", 7, 7);
x_149 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_148);
x_150 = lean_mk_string_unchecked("↓", 3, 1);
lean_inc(x_125);
x_151 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_151, 0, x_125);
lean_ctor_set(x_151, 1, x_150);
lean_inc(x_125);
x_152 = l_Lean_Syntax_node1(x_125, x_149, x_151);
lean_inc(x_147);
lean_inc(x_125);
x_153 = l_Lean_Syntax_node1(x_125, x_147, x_152);
x_154 = l_Array_mkArray0(lean_box(0));
lean_inc(x_125);
x_155 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_155, 0, x_125);
lean_ctor_set(x_155, 1, x_147);
lean_ctor_set(x_155, 2, x_154);
x_156 = l_Lean_Syntax_node3(x_125, x_145, x_153, x_155, x_123);
x_42 = x_27;
x_43 = x_156;
x_44 = x_143;
goto block_47;
}
}
else
{
lean_object* x_157; uint8_t x_158; 
x_157 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_mkSimpOnly_spec__8_spec__8___lam__0(x_117, x_8, x_9, x_10, x_11, x_122);
x_158 = !lean_is_exclusive(x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_159 = lean_ctor_get(x_157, 0);
x_160 = lean_ctor_get(x_157, 1);
x_161 = lean_st_ref_get(x_11, x_160);
x_162 = !lean_is_exclusive(x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_163 = lean_ctor_get(x_161, 1);
x_164 = lean_ctor_get(x_161, 0);
lean_dec(x_164);
x_165 = lean_mk_string_unchecked("simpLemma", 9, 9);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_166 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_165);
x_167 = lean_mk_string_unchecked("null", 4, 4);
x_168 = l_Lean_Name_mkStr1(x_167);
x_169 = lean_mk_string_unchecked("simpPre", 7, 7);
x_170 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_169);
x_171 = lean_mk_string_unchecked("↓", 3, 1);
lean_inc(x_159);
lean_ctor_set_tag(x_161, 2);
lean_ctor_set(x_161, 1, x_171);
lean_ctor_set(x_161, 0, x_159);
lean_inc(x_159);
x_172 = l_Lean_Syntax_node1(x_159, x_170, x_161);
lean_inc(x_168);
lean_inc(x_159);
x_173 = l_Lean_Syntax_node1(x_159, x_168, x_172);
x_174 = lean_mk_string_unchecked("patternIgnore", 13, 13);
x_175 = l_Lean_Name_mkStr1(x_174);
x_176 = lean_mk_string_unchecked("token", 5, 5);
x_177 = lean_mk_string_unchecked("← ", 4, 2);
x_178 = l_Lean_Name_mkStr2(x_176, x_177);
x_179 = lean_mk_string_unchecked("←", 3, 1);
lean_inc(x_159);
lean_ctor_set_tag(x_157, 2);
lean_ctor_set(x_157, 1, x_179);
lean_inc(x_159);
x_180 = l_Lean_Syntax_node1(x_159, x_178, x_157);
lean_inc(x_159);
x_181 = l_Lean_Syntax_node1(x_159, x_175, x_180);
lean_inc(x_159);
x_182 = l_Lean_Syntax_node1(x_159, x_168, x_181);
x_183 = l_Lean_Syntax_node3(x_159, x_166, x_173, x_182, x_123);
x_42 = x_27;
x_43 = x_183;
x_44 = x_163;
goto block_47;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_184 = lean_ctor_get(x_161, 1);
lean_inc(x_184);
lean_dec(x_161);
x_185 = lean_mk_string_unchecked("simpLemma", 9, 9);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_186 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_185);
x_187 = lean_mk_string_unchecked("null", 4, 4);
x_188 = l_Lean_Name_mkStr1(x_187);
x_189 = lean_mk_string_unchecked("simpPre", 7, 7);
x_190 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_189);
x_191 = lean_mk_string_unchecked("↓", 3, 1);
lean_inc(x_159);
x_192 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_192, 0, x_159);
lean_ctor_set(x_192, 1, x_191);
lean_inc(x_159);
x_193 = l_Lean_Syntax_node1(x_159, x_190, x_192);
lean_inc(x_188);
lean_inc(x_159);
x_194 = l_Lean_Syntax_node1(x_159, x_188, x_193);
x_195 = lean_mk_string_unchecked("patternIgnore", 13, 13);
x_196 = l_Lean_Name_mkStr1(x_195);
x_197 = lean_mk_string_unchecked("token", 5, 5);
x_198 = lean_mk_string_unchecked("← ", 4, 2);
x_199 = l_Lean_Name_mkStr2(x_197, x_198);
x_200 = lean_mk_string_unchecked("←", 3, 1);
lean_inc(x_159);
lean_ctor_set_tag(x_157, 2);
lean_ctor_set(x_157, 1, x_200);
lean_inc(x_159);
x_201 = l_Lean_Syntax_node1(x_159, x_199, x_157);
lean_inc(x_159);
x_202 = l_Lean_Syntax_node1(x_159, x_196, x_201);
lean_inc(x_159);
x_203 = l_Lean_Syntax_node1(x_159, x_188, x_202);
x_204 = l_Lean_Syntax_node3(x_159, x_186, x_194, x_203, x_123);
x_42 = x_27;
x_43 = x_204;
x_44 = x_184;
goto block_47;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_205 = lean_ctor_get(x_157, 0);
x_206 = lean_ctor_get(x_157, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_157);
x_207 = lean_st_ref_get(x_11, x_206);
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
x_210 = lean_mk_string_unchecked("simpLemma", 9, 9);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_211 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_210);
x_212 = lean_mk_string_unchecked("null", 4, 4);
x_213 = l_Lean_Name_mkStr1(x_212);
x_214 = lean_mk_string_unchecked("simpPre", 7, 7);
x_215 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_214);
x_216 = lean_mk_string_unchecked("↓", 3, 1);
lean_inc(x_205);
if (lean_is_scalar(x_209)) {
 x_217 = lean_alloc_ctor(2, 2, 0);
} else {
 x_217 = x_209;
 lean_ctor_set_tag(x_217, 2);
}
lean_ctor_set(x_217, 0, x_205);
lean_ctor_set(x_217, 1, x_216);
lean_inc(x_205);
x_218 = l_Lean_Syntax_node1(x_205, x_215, x_217);
lean_inc(x_213);
lean_inc(x_205);
x_219 = l_Lean_Syntax_node1(x_205, x_213, x_218);
x_220 = lean_mk_string_unchecked("patternIgnore", 13, 13);
x_221 = l_Lean_Name_mkStr1(x_220);
x_222 = lean_mk_string_unchecked("token", 5, 5);
x_223 = lean_mk_string_unchecked("← ", 4, 2);
x_224 = l_Lean_Name_mkStr2(x_222, x_223);
x_225 = lean_mk_string_unchecked("←", 3, 1);
lean_inc(x_205);
x_226 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_226, 0, x_205);
lean_ctor_set(x_226, 1, x_225);
lean_inc(x_205);
x_227 = l_Lean_Syntax_node1(x_205, x_224, x_226);
lean_inc(x_205);
x_228 = l_Lean_Syntax_node1(x_205, x_221, x_227);
lean_inc(x_205);
x_229 = l_Lean_Syntax_node1(x_205, x_213, x_228);
x_230 = l_Lean_Syntax_node3(x_205, x_211, x_219, x_229, x_123);
x_42 = x_27;
x_43 = x_230;
x_44 = x_208;
goto block_47;
}
}
}
else
{
if (x_56 == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_231 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_mkSimpOnly_spec__8_spec__8___lam__0(x_117, x_8, x_9, x_10, x_11, x_122);
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
lean_dec(x_231);
x_234 = lean_st_ref_get(x_11, x_233);
x_235 = lean_ctor_get(x_234, 1);
lean_inc(x_235);
lean_dec(x_234);
x_236 = lean_mk_string_unchecked("simpLemma", 9, 9);
x_237 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_236);
x_238 = lean_mk_string_unchecked("null", 4, 4);
x_239 = l_Lean_Name_mkStr1(x_238);
x_240 = l_Array_mkArray0(lean_box(0));
lean_inc(x_232);
x_241 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_241, 0, x_232);
lean_ctor_set(x_241, 1, x_239);
lean_ctor_set(x_241, 2, x_240);
lean_inc(x_241);
x_242 = l_Lean_Syntax_node3(x_232, x_237, x_241, x_241, x_123);
x_42 = x_27;
x_43 = x_242;
x_44 = x_235;
goto block_47;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; 
x_243 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_mkSimpOnly_spec__8_spec__8___lam__0(x_117, x_8, x_9, x_10, x_11, x_122);
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
lean_dec(x_243);
x_246 = lean_st_ref_get(x_11, x_245);
x_247 = !lean_is_exclusive(x_246);
if (x_247 == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_248 = lean_ctor_get(x_246, 1);
x_249 = lean_ctor_get(x_246, 0);
lean_dec(x_249);
x_250 = lean_mk_string_unchecked("simpLemma", 9, 9);
x_251 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_250);
x_252 = lean_mk_string_unchecked("null", 4, 4);
x_253 = l_Lean_Name_mkStr1(x_252);
x_254 = l_Array_mkArray0(lean_box(0));
lean_inc(x_253);
lean_inc(x_244);
x_255 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_255, 0, x_244);
lean_ctor_set(x_255, 1, x_253);
lean_ctor_set(x_255, 2, x_254);
x_256 = lean_mk_string_unchecked("patternIgnore", 13, 13);
x_257 = l_Lean_Name_mkStr1(x_256);
x_258 = lean_mk_string_unchecked("token", 5, 5);
x_259 = lean_mk_string_unchecked("← ", 4, 2);
x_260 = l_Lean_Name_mkStr2(x_258, x_259);
x_261 = lean_mk_string_unchecked("←", 3, 1);
lean_inc(x_244);
lean_ctor_set_tag(x_246, 2);
lean_ctor_set(x_246, 1, x_261);
lean_ctor_set(x_246, 0, x_244);
lean_inc(x_244);
x_262 = l_Lean_Syntax_node1(x_244, x_260, x_246);
lean_inc(x_244);
x_263 = l_Lean_Syntax_node1(x_244, x_257, x_262);
lean_inc(x_244);
x_264 = l_Lean_Syntax_node1(x_244, x_253, x_263);
x_265 = l_Lean_Syntax_node3(x_244, x_251, x_255, x_264, x_123);
x_42 = x_27;
x_43 = x_265;
x_44 = x_248;
goto block_47;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_266 = lean_ctor_get(x_246, 1);
lean_inc(x_266);
lean_dec(x_246);
x_267 = lean_mk_string_unchecked("simpLemma", 9, 9);
x_268 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_267);
x_269 = lean_mk_string_unchecked("null", 4, 4);
x_270 = l_Lean_Name_mkStr1(x_269);
x_271 = l_Array_mkArray0(lean_box(0));
lean_inc(x_270);
lean_inc(x_244);
x_272 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_272, 0, x_244);
lean_ctor_set(x_272, 1, x_270);
lean_ctor_set(x_272, 2, x_271);
x_273 = lean_mk_string_unchecked("patternIgnore", 13, 13);
x_274 = l_Lean_Name_mkStr1(x_273);
x_275 = lean_mk_string_unchecked("token", 5, 5);
x_276 = lean_mk_string_unchecked("← ", 4, 2);
x_277 = l_Lean_Name_mkStr2(x_275, x_276);
x_278 = lean_mk_string_unchecked("←", 3, 1);
lean_inc(x_244);
x_279 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_279, 0, x_244);
lean_ctor_set(x_279, 1, x_278);
lean_inc(x_244);
x_280 = l_Lean_Syntax_node1(x_244, x_277, x_279);
lean_inc(x_244);
x_281 = l_Lean_Syntax_node1(x_244, x_274, x_280);
lean_inc(x_244);
x_282 = l_Lean_Syntax_node1(x_244, x_270, x_281);
x_283 = l_Lean_Syntax_node3(x_244, x_268, x_272, x_282, x_123);
x_42 = x_27;
x_43 = x_283;
x_44 = x_266;
goto block_47;
}
}
}
}
else
{
uint8_t x_284; 
lean_dec(x_41);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_284 = !lean_is_exclusive(x_118);
if (x_284 == 0)
{
return x_118;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_285 = lean_ctor_get(x_118, 0);
x_286 = lean_ctor_get(x_118, 1);
lean_inc(x_286);
lean_inc(x_285);
lean_dec(x_118);
x_287 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_287, 0, x_285);
lean_ctor_set(x_287, 1, x_286);
return x_287;
}
}
}
else
{
lean_object* x_288; uint8_t x_289; 
x_288 = lean_box(0);
x_289 = lean_unbox(x_288);
x_57 = x_289;
goto block_116;
}
}
block_292:
{
if (x_291 == 0)
{
x_57 = x_291;
goto block_116;
}
else
{
goto block_290;
}
}
}
case 1:
{
lean_object* x_302; lean_object* x_303; 
x_302 = lean_ctor_get(x_26, 0);
lean_inc(x_302);
lean_dec(x_26);
lean_inc(x_2);
x_303 = lean_local_ctx_find(x_2, x_302);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_20);
x_304 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_304, 0, x_27);
lean_ctor_set(x_304, 1, x_41);
x_13 = x_304;
x_14 = x_12;
goto block_19;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_329; lean_object* x_330; uint8_t x_331; uint8_t x_334; lean_object* x_335; uint8_t x_336; lean_object* x_337; lean_object* x_338; lean_object* x_341; lean_object* x_342; uint8_t x_343; uint8_t x_344; uint8_t x_347; lean_object* x_348; lean_object* x_349; uint8_t x_352; lean_object* x_356; uint8_t x_357; 
x_305 = lean_ctor_get(x_303, 0);
lean_inc(x_305);
lean_dec(x_303);
x_356 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_20);
lean_inc(x_3);
x_357 = l_Lean_Syntax_isOfKind(x_3, x_356);
lean_dec(x_356);
if (x_357 == 0)
{
goto block_359;
}
else
{
uint8_t x_360; 
x_360 = l_Lean_LocalDecl_hasValue(x_305);
if (x_360 == 0)
{
goto block_359;
}
else
{
lean_object* x_361; uint8_t x_362; 
x_361 = lean_box(0);
x_362 = lean_unbox(x_361);
x_352 = x_362;
goto block_355;
}
}
block_310:
{
lean_object* x_309; 
x_309 = lean_ctor_get(x_305, 1);
lean_inc(x_309);
lean_dec(x_305);
x_33 = x_308;
x_34 = x_306;
x_35 = x_307;
x_36 = x_309;
goto block_40;
}
block_315:
{
lean_object* x_314; 
x_314 = lean_ctor_get(x_313, 1);
lean_inc(x_314);
lean_dec(x_313);
x_306 = x_311;
x_307 = x_312;
x_308 = x_314;
goto block_310;
}
block_328:
{
lean_object* x_319; 
x_319 = l_Lean_LocalContext_findFromUserName_x3f(x_2, x_318);
lean_dec(x_318);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_320 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
x_321 = lean_mk_string_unchecked("Option.get!", 11, 11);
x_322 = lean_unsigned_to_nat(21u);
x_323 = lean_unsigned_to_nat(14u);
x_324 = lean_mk_string_unchecked("value is none", 13, 13);
x_325 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_320, x_321, x_322, x_323, x_324);
lean_dec(x_324);
lean_dec(x_321);
lean_dec(x_320);
x_326 = l_panic___at___Lean_LocalDecl_setBinderInfo_spec__0(x_325);
x_311 = x_316;
x_312 = x_317;
x_313 = x_326;
goto block_315;
}
else
{
lean_object* x_327; 
x_327 = lean_ctor_get(x_319, 0);
lean_inc(x_327);
lean_dec(x_319);
x_311 = x_316;
x_312 = x_317;
x_313 = x_327;
goto block_315;
}
}
block_333:
{
if (x_331 == 0)
{
lean_dec(x_330);
lean_dec(x_329);
lean_dec(x_305);
goto block_32;
}
else
{
lean_object* x_332; 
x_332 = lean_ctor_get(x_305, 2);
lean_inc(x_332);
x_316 = x_329;
x_317 = x_330;
x_318 = x_332;
goto block_328;
}
}
block_340:
{
uint8_t x_339; 
x_339 = l_Lean_Name_hasMacroScopes(x_338);
lean_dec(x_338);
if (x_339 == 0)
{
x_329 = x_335;
x_330 = x_337;
x_331 = x_334;
goto block_333;
}
else
{
x_329 = x_335;
x_330 = x_337;
x_331 = x_336;
goto block_333;
}
}
block_346:
{
if (x_344 == 0)
{
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_305);
goto block_32;
}
else
{
lean_object* x_345; 
x_345 = lean_ctor_get(x_305, 2);
lean_inc(x_345);
x_334 = x_344;
x_335 = x_341;
x_336 = x_343;
x_337 = x_342;
x_338 = x_345;
goto block_340;
}
}
block_351:
{
uint8_t x_350; 
lean_inc(x_349);
x_350 = lean_is_inaccessible_user_name(x_349);
if (x_350 == 0)
{
x_341 = x_349;
x_342 = x_348;
x_343 = x_347;
x_344 = x_21;
goto block_346;
}
else
{
x_341 = x_349;
x_342 = x_348;
x_343 = x_347;
x_344 = x_347;
goto block_346;
}
}
block_355:
{
if (lean_obj_tag(x_41) == 0)
{
lean_dec(x_305);
x_28 = x_41;
goto block_30;
}
else
{
lean_object* x_353; lean_object* x_354; 
x_353 = lean_ctor_get(x_41, 0);
lean_inc(x_353);
lean_dec(x_41);
x_354 = lean_ctor_get(x_305, 2);
lean_inc(x_354);
x_347 = x_352;
x_348 = x_353;
x_349 = x_354;
goto block_351;
}
}
block_359:
{
if (x_357 == 0)
{
x_352 = x_357;
goto block_355;
}
else
{
lean_object* x_358; 
lean_dec(x_305);
x_358 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_358, 0, x_27);
lean_ctor_set(x_358, 1, x_41);
x_13 = x_358;
x_14 = x_12;
goto block_19;
}
}
}
}
case 2:
{
uint8_t x_363; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_20);
x_363 = !lean_is_exclusive(x_26);
if (x_363 == 0)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_364 = lean_ctor_get(x_26, 1);
x_365 = lean_ctor_get(x_26, 0);
lean_dec(x_365);
x_366 = lean_array_push(x_27, x_364);
lean_ctor_set_tag(x_26, 0);
lean_ctor_set(x_26, 1, x_41);
lean_ctor_set(x_26, 0, x_366);
x_13 = x_26;
x_14 = x_12;
goto block_19;
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_367 = lean_ctor_get(x_26, 1);
lean_inc(x_367);
lean_dec(x_26);
x_368 = lean_array_push(x_27, x_367);
x_369 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_369, 0, x_368);
lean_ctor_set(x_369, 1, x_41);
x_13 = x_369;
x_14 = x_12;
goto block_19;
}
}
default: 
{
lean_object* x_370; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_20);
x_370 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_370, 0, x_27);
lean_ctor_set(x_370, 1, x_41);
x_13 = x_370;
x_14 = x_12;
goto block_19;
}
}
block_30:
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_13 = x_29;
x_14 = x_12;
goto block_19;
}
block_32:
{
lean_object* x_31; 
x_31 = lean_box(0);
x_28 = x_31;
goto block_30;
}
block_40:
{
uint8_t x_37; 
x_37 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_33, x_36);
lean_dec(x_36);
lean_dec(x_33);
if (x_37 == 0)
{
lean_dec(x_35);
lean_dec(x_34);
goto block_32;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_array_push(x_35, x_34);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_28 = x_39;
goto block_30;
}
}
block_47:
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_array_push(x_42, x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_41);
x_13 = x_46;
x_14 = x_44;
goto block_19;
}
block_53:
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_array_push(x_48, x_49);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_41);
x_13 = x_52;
x_14 = x_50;
goto block_19;
}
}
block_19:
{
lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_add(x_6, x_16);
x_18 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_mkSimpOnly_spec__8_spec__8(x_1, x_2, x_3, x_4, x_5, x_17, x_13, x_8, x_9, x_10, x_11, x_14);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_mkSimpOnly_spec__10___redArg(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_2, x_1);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; 
x_9 = lean_st_ref_get(x_5, x_6);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = lean_mk_string_unchecked("Lean", 4, 4);
x_13 = lean_mk_string_unchecked("Parser", 6, 6);
x_14 = lean_mk_string_unchecked("Tactic", 6, 6);
x_15 = lean_array_uget(x_3, x_2);
x_16 = lean_array_uset(x_3, x_2, x_11);
x_17 = lean_ctor_get(x_4, 5);
x_18 = lean_box(0);
x_19 = lean_unbox(x_18);
x_20 = l_Lean_SourceInfo_fromRef(x_17, x_19);
x_21 = lean_mk_string_unchecked("simpLemma", 9, 9);
x_22 = l_Lean_Name_mkStr4(x_12, x_13, x_14, x_21);
x_23 = lean_mk_string_unchecked("null", 4, 4);
x_24 = l_Lean_Name_mkStr1(x_23);
x_25 = l_Array_mkArray0(lean_box(0));
lean_inc(x_20);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_mk_syntax_ident(x_15);
lean_inc(x_26);
x_28 = l_Lean_Syntax_node3(x_20, x_22, x_26, x_26, x_27);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_usize_of_nat(x_29);
x_31 = lean_usize_add(x_2, x_30);
x_32 = lean_array_uset(x_16, x_2, x_28);
x_2 = x_31;
x_3 = x_32;
x_6 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_mkSimpOnly_spec__10(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_mkSimpOnly_spec__10___redArg(x_1, x_2, x_3, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpOnly(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_14 = lean_mk_string_unchecked("Lean", 4, 4);
x_15 = lean_mk_string_unchecked("Parser", 6, 6);
x_16 = lean_mk_string_unchecked("Tactic", 6, 6);
x_118 = lean_unsigned_to_nat(3u);
x_119 = l_Lean_Syntax_getArg(x_1, x_118);
x_120 = l_Lean_Syntax_isNone(x_119);
lean_dec(x_119);
if (x_120 == 0)
{
lean_inc(x_1);
x_17 = x_1;
x_18 = x_3;
x_19 = x_4;
x_20 = x_5;
x_21 = x_6;
x_22 = x_7;
goto block_117;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_121 = lean_mk_string_unchecked("only", 4, 4);
x_122 = l_Lean_mkAtom(x_121);
x_123 = lean_unsigned_to_nat(1u);
x_124 = lean_mk_empty_array_with_capacity(x_123);
x_125 = lean_array_push(x_124, x_122);
x_126 = lean_mk_string_unchecked("null", 4, 4);
x_127 = l_Lean_Name_mkStr1(x_126);
x_128 = lean_box(2);
x_129 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_127);
lean_ctor_set(x_129, 2, x_125);
lean_inc(x_1);
x_130 = l_Lean_Syntax_setArg(x_1, x_118, x_129);
x_17 = x_130;
x_18 = x_3;
x_19 = x_4;
x_20 = x_5;
x_21 = x_6;
x_22 = x_7;
goto block_117;
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Elab_Tactic_setSimpParams(x_8, x_9);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
block_117:
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_st_ref_get(x_21, x_22);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; lean_object* x_35; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_mk_empty_array_with_capacity(x_27);
lean_inc(x_28);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_ctor_get(x_18, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_25, 0);
lean_inc(x_31);
lean_dec(x_25);
x_32 = l_Lean_Meta_Simp_UsedSimps_toArray(x_2);
lean_ctor_set(x_23, 1, x_29);
lean_ctor_set(x_23, 0, x_28);
x_33 = lean_array_size(x_32);
x_34 = lean_usize_of_nat(x_27);
lean_inc(x_21);
lean_inc(x_20);
x_35 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_mkSimpOnly_spec__8(x_31, x_30, x_1, x_32, x_33, x_34, x_23, x_18, x_19, x_20, x_21, x_26);
lean_dec(x_32);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_ctor_get(x_36, 0);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_st_ref_get(x_21, x_38);
lean_dec(x_21);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_42 = lean_ctor_get(x_40, 1);
x_43 = lean_ctor_get(x_40, 0);
lean_dec(x_43);
x_44 = lean_ctor_get(x_20, 5);
lean_inc(x_44);
lean_dec(x_20);
x_45 = lean_box(0);
x_46 = lean_unbox(x_45);
x_47 = l_Lean_SourceInfo_fromRef(x_44, x_46);
lean_dec(x_44);
x_48 = lean_mk_string_unchecked("simpStar", 8, 8);
x_49 = l_Lean_Name_mkStr4(x_14, x_15, x_16, x_48);
x_50 = lean_mk_string_unchecked("*", 1, 1);
lean_inc(x_47);
lean_ctor_set_tag(x_40, 2);
lean_ctor_set(x_40, 1, x_50);
lean_ctor_set(x_40, 0, x_47);
x_51 = l_Lean_Syntax_node1(x_47, x_49, x_40);
x_52 = lean_array_push(x_39, x_51);
x_8 = x_17;
x_9 = x_52;
x_10 = x_42;
goto block_13;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_53 = lean_ctor_get(x_40, 1);
lean_inc(x_53);
lean_dec(x_40);
x_54 = lean_ctor_get(x_20, 5);
lean_inc(x_54);
lean_dec(x_20);
x_55 = lean_box(0);
x_56 = lean_unbox(x_55);
x_57 = l_Lean_SourceInfo_fromRef(x_54, x_56);
lean_dec(x_54);
x_58 = lean_mk_string_unchecked("simpStar", 8, 8);
x_59 = l_Lean_Name_mkStr4(x_14, x_15, x_16, x_58);
x_60 = lean_mk_string_unchecked("*", 1, 1);
lean_inc(x_57);
x_61 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_61, 0, x_57);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_Syntax_node1(x_57, x_59, x_61);
x_63 = lean_array_push(x_39, x_62);
x_8 = x_17;
x_9 = x_63;
x_10 = x_53;
goto block_13;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; size_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_64 = lean_ctor_get(x_35, 1);
lean_inc(x_64);
lean_dec(x_35);
x_65 = lean_ctor_get(x_36, 0);
lean_inc(x_65);
lean_dec(x_36);
x_66 = lean_ctor_get(x_37, 0);
lean_inc(x_66);
lean_dec(x_37);
x_67 = lean_array_size(x_66);
x_68 = l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_mkSimpOnly_spec__10___redArg(x_67, x_34, x_66, x_20, x_21, x_64);
lean_dec(x_21);
lean_dec(x_20);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Array_append(lean_box(0), x_65, x_69);
lean_dec(x_69);
x_8 = x_17;
x_9 = x_71;
x_10 = x_70;
goto block_13;
}
}
else
{
uint8_t x_72; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_72 = !lean_is_exclusive(x_35);
if (x_72 == 0)
{
return x_35;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_35, 0);
x_74 = lean_ctor_get(x_35, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_35);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; size_t x_85; size_t x_86; lean_object* x_87; 
x_76 = lean_ctor_get(x_23, 0);
x_77 = lean_ctor_get(x_23, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_23);
x_78 = lean_unsigned_to_nat(0u);
x_79 = lean_mk_empty_array_with_capacity(x_78);
lean_inc(x_79);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = lean_ctor_get(x_18, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_76, 0);
lean_inc(x_82);
lean_dec(x_76);
x_83 = l_Lean_Meta_Simp_UsedSimps_toArray(x_2);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_79);
lean_ctor_set(x_84, 1, x_80);
x_85 = lean_array_size(x_83);
x_86 = lean_usize_of_nat(x_78);
lean_inc(x_21);
lean_inc(x_20);
x_87 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_mkSimpOnly_spec__8(x_82, x_81, x_1, x_83, x_85, x_86, x_84, x_18, x_19, x_20, x_21, x_77);
lean_dec(x_83);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
x_91 = lean_ctor_get(x_88, 0);
lean_inc(x_91);
lean_dec(x_88);
x_92 = lean_st_ref_get(x_21, x_90);
lean_dec(x_21);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_94 = x_92;
} else {
 lean_dec_ref(x_92);
 x_94 = lean_box(0);
}
x_95 = lean_ctor_get(x_20, 5);
lean_inc(x_95);
lean_dec(x_20);
x_96 = lean_box(0);
x_97 = lean_unbox(x_96);
x_98 = l_Lean_SourceInfo_fromRef(x_95, x_97);
lean_dec(x_95);
x_99 = lean_mk_string_unchecked("simpStar", 8, 8);
x_100 = l_Lean_Name_mkStr4(x_14, x_15, x_16, x_99);
x_101 = lean_mk_string_unchecked("*", 1, 1);
lean_inc(x_98);
if (lean_is_scalar(x_94)) {
 x_102 = lean_alloc_ctor(2, 2, 0);
} else {
 x_102 = x_94;
 lean_ctor_set_tag(x_102, 2);
}
lean_ctor_set(x_102, 0, x_98);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Lean_Syntax_node1(x_98, x_100, x_102);
x_104 = lean_array_push(x_91, x_103);
x_8 = x_17;
x_9 = x_104;
x_10 = x_93;
goto block_13;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; size_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_105 = lean_ctor_get(x_87, 1);
lean_inc(x_105);
lean_dec(x_87);
x_106 = lean_ctor_get(x_88, 0);
lean_inc(x_106);
lean_dec(x_88);
x_107 = lean_ctor_get(x_89, 0);
lean_inc(x_107);
lean_dec(x_89);
x_108 = lean_array_size(x_107);
x_109 = l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_mkSimpOnly_spec__10___redArg(x_108, x_86, x_107, x_20, x_21, x_105);
lean_dec(x_21);
lean_dec(x_20);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = l_Array_append(lean_box(0), x_106, x_110);
lean_dec(x_110);
x_8 = x_17;
x_9 = x_112;
x_10 = x_111;
goto block_13;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_113 = lean_ctor_get(x_87, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_87, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_115 = x_87;
} else {
 lean_dec_ref(x_87);
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
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___Lean_resolveLocalName_loop___at___Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_resolveGlobalName___at___Lean_resolveLocalName_loop___at___Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___Lean_resolveLocalName_loop___at___Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_resolveGlobalName___at___Lean_resolveLocalName_loop___at___Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName_loop___at___Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_Lean_resolveLocalName_loop___at___Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName_loop___at___Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l_Lean_resolveLocalName_loop___at___Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0___lam__0(x_1, x_2, x_3, x_4, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_unresolveNameGlobal_unresolveNameCore___at___Lean_unresolveNameGlobal___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__3_spec__3_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forIn_x27_loop___at___Lean_unresolveNameGlobal_unresolveNameCore___at___Lean_unresolveNameGlobal___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__3_spec__3_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_unresolveNameGlobal_unresolveNameCore___at___Lean_unresolveNameGlobal___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__3_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_x27_loop___at___Lean_unresolveNameGlobal_unresolveNameCore___at___Lean_unresolveNameGlobal___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__3_spec__3_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___at___Lean_unresolveNameGlobal___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_unresolveNameGlobal_unresolveNameCore___at___Lean_unresolveNameGlobal___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__3_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_unresolveNameGlobal___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__3_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_unresolveNameGlobal___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__3_spec__5(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__3___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_unresolveNameGlobal___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__3___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_unresolveNameGlobal___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0_spec__3(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0___lam__0(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_mkSimpOnly_spec__8_spec__8___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_mkSimpOnly_spec__8_spec__8___lam__0(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_mkSimpOnly_spec__8_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_mkSimpOnly_spec__8_spec__8(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_mkSimpOnly_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_mkSimpOnly_spec__8(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_mkSimpOnly_spec__10___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_mkSimpOnly_spec__10___redArg(x_7, x_8, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_mkSimpOnly_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_mkSimpOnly_spec__10(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpOnly___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_mkSimpOnly(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___Lean_Elab_Tactic_traceSimpCall_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_box(0);
x_9 = lean_box(0);
x_10 = lean_unbox(x_8);
x_11 = lean_unbox(x_9);
x_12 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__0(x_1, x_2, x_10, x_11, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_traceSimpCall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_Elab_Tactic_mkSimpOnly(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
lean_dec(x_1);
x_13 = lean_mk_string_unchecked("Try this: ", 10, 10);
x_14 = l_Lean_stringToMessageData(x_13);
lean_dec(x_13);
x_15 = l_Lean_MessageData_ofSyntax(x_9);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_mk_string_unchecked("", 0, 0);
x_18 = l_Lean_stringToMessageData(x_17);
lean_dec(x_17);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_logInfoAt___at___Lean_Elab_Tactic_traceSimpCall_spec__0(x_12, x_19, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_12);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_8);
if (x_21 == 0)
{
return x_8;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_8, 0);
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_8);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___Lean_Elab_Tactic_traceSimpCall_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_logInfoAt___at___Lean_Elab_Tactic_traceSimpCall_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_traceSimpCall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_traceSimpCall(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpLocation_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Tactic_getMainGoal(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; lean_object* x_26; lean_object* x_27; size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_18);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_unsigned_to_nat(0u);
lean_inc(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_18);
x_23 = lean_unsigned_to_nat(2u);
x_24 = lean_unsigned_to_nat(5u);
x_25 = lean_usize_of_nat(x_24);
x_26 = lean_usize_to_nat(x_25);
x_27 = lean_nat_pow(x_23, x_26);
lean_dec(x_26);
x_28 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_29 = lean_usize_to_nat(x_28);
x_30 = lean_mk_empty_array_with_capacity(x_29);
lean_dec(x_29);
lean_inc(x_30);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_20);
lean_ctor_set(x_32, 3, x_20);
lean_ctor_set_usize(x_32, 4, x_25);
lean_inc(x_19);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_19);
lean_ctor_set(x_33, 1, x_19);
lean_ctor_set(x_33, 2, x_22);
lean_ctor_set(x_33, 3, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_21);
lean_ctor_set(x_34, 1, x_33);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_35 = l_Lean_Meta_simpGoal(x_16, x_1, x_2, x_3, x_5, x_4, x_34, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_box(0);
x_41 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_40, x_7, x_10, x_11, x_12, x_13, x_38);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
lean_ctor_set(x_41, 0, x_39);
return x_41;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_39);
x_46 = !lean_is_exclusive(x_41);
if (x_46 == 0)
{
return x_41;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_41, 0);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_41);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_37, 0);
lean_inc(x_50);
lean_dec(x_37);
x_51 = lean_ctor_get(x_35, 1);
lean_inc(x_51);
lean_dec(x_35);
x_52 = lean_ctor_get(x_36, 1);
lean_inc(x_52);
lean_dec(x_36);
x_53 = !lean_is_exclusive(x_50);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_50, 1);
x_55 = lean_ctor_get(x_50, 0);
lean_dec(x_55);
x_56 = lean_box(0);
lean_ctor_set_tag(x_50, 1);
lean_ctor_set(x_50, 1, x_56);
lean_ctor_set(x_50, 0, x_54);
x_57 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_50, x_7, x_10, x_11, x_12, x_13, x_51);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
lean_ctor_set(x_57, 0, x_52);
return x_57;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_52);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
else
{
uint8_t x_62; 
lean_dec(x_52);
x_62 = !lean_is_exclusive(x_57);
if (x_62 == 0)
{
return x_57;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_57, 0);
x_64 = lean_ctor_get(x_57, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_57);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_50, 1);
lean_inc(x_66);
lean_dec(x_50);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_68, x_7, x_10, x_11, x_12, x_13, x_51);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_52);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_52);
x_73 = lean_ctor_get(x_69, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_75 = x_69;
} else {
 lean_dec_ref(x_69);
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
}
else
{
uint8_t x_77; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_77 = !lean_is_exclusive(x_35);
if (x_77 == 0)
{
return x_35;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_35, 0);
x_79 = lean_ctor_get(x_35, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_35);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_15);
if (x_81 == 0)
{
return x_15;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_15, 0);
x_83 = lean_ctor_get(x_15, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_15);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpLocation_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Lean_Elab_Tactic_simpLocation_go(x_1, x_2, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpLocation___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_getMainGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_16 = l_Lean_MVarId_getNondepPropHyps(x_14, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(1);
x_20 = lean_unbox(x_19);
x_21 = l_Lean_Elab_Tactic_simpLocation_go(x_1, x_2, x_3, x_17, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpLocation___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = l_Lean_Elab_Tactic_getFVarIds(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Elab_Tactic_simpLocation_go(x_2, x_3, x_4, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpLocation(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_simpLocation___lam__0___boxed), 12, 3);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_3);
x_15 = l_Lean_Elab_Tactic_withMainContext___redArg(x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
x_17 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_dec(x_4);
x_18 = lean_box(x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_simpLocation___lam__1___boxed), 14, 5);
lean_closure_set(x_19, 0, x_16);
lean_closure_set(x_19, 1, x_1);
lean_closure_set(x_19, 2, x_2);
lean_closure_set(x_19, 3, x_3);
lean_closure_set(x_19, 4, x_18);
x_20 = l_Lean_Elab_Tactic_withMainContext___redArg(x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpLocation___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_simpLocation___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpLocation___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Lean_Elab_Tactic_simpLocation___lam__1(x_1, x_2, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_10);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpLocation___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_simpLocation(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withSimpDiagnostics(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_11 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_Simp_reportDiag(x_12, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimp___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_unsigned_to_nat(5u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = l_Lean_Elab_Tactic_expandOptLocation(x_15);
lean_dec(x_15);
x_17 = l_Lean_Elab_Tactic_simpLocation(x_2, x_3, x_4, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimp___lam__1(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_Elab_Tactic_mkSimpContext(x_1, x_2, x_3, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 2);
lean_inc(x_19);
lean_dec(x_15);
lean_inc(x_1);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimp___lam__0___boxed), 13, 3);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_17);
lean_closure_set(x_20, 2, x_18);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_21 = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(x_19, x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
lean_dec(x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_24 = x_21;
} else {
 lean_dec_ref(x_21);
 x_24 = lean_box(0);
}
x_29 = lean_ctor_get(x_11, 2);
lean_inc(x_29);
x_30 = l_Lean_Elab_Tactic_tactic_simp_trace;
x_31 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_29, x_30);
lean_dec(x_29);
if (x_31 == 0)
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_25 = x_23;
goto block_28;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_22, 0);
lean_inc(x_32);
x_33 = l_Lean_Elab_Tactic_traceSimpCall(x_1, x_32, x_9, x_10, x_11, x_12, x_23);
lean_dec(x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_25 = x_34;
goto block_28;
}
else
{
uint8_t x_35; 
lean_dec(x_24);
lean_dec(x_22);
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_33, 0);
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_33);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
block_28:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
if (lean_is_scalar(x_24)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_24;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8_t x_39; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_21);
if (x_39 == 0)
{
return x_21;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_21, 0);
x_41 = lean_ctor_get(x_21, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_21);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_14);
if (x_43 == 0)
{
return x_14;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_14, 0);
x_45 = lean_ctor_get(x_14, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_14);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_box(0);
x_12 = lean_box(0);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_getSimpTheorems___boxed), 3, 0);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimp___lam__1___boxed), 13, 4);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics), 10, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = l_Lean_Elab_Tactic_withMainContext___redArg(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimp___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_evalSimp___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimp___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = l_Lean_Elab_Tactic_evalSimp___lam__1(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalSimp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimp__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("simp", 4, 4);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("evalSimp", 8, 8);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimp___boxed), 10, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("evalSimp", 8, 8);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(432u);
x_8 = lean_unsigned_to_nat(42u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(438u);
x_11 = lean_unsigned_to_nat(19u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(46u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(54u);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_addBuiltinDeclarationRanges(x_6, x_19, x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAll___lam__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_Elab_Tactic_mkSimpContext(x_1, x_2, x_3, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l_Lean_Elab_Tactic_getMainGoal(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; lean_object* x_30; lean_object* x_31; size_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_22);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_unsigned_to_nat(0u);
lean_inc(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_22);
x_27 = lean_unsigned_to_nat(2u);
x_28 = lean_unsigned_to_nat(5u);
x_29 = lean_usize_of_nat(x_28);
x_30 = lean_usize_to_nat(x_29);
x_31 = lean_nat_pow(x_27, x_30);
lean_dec(x_30);
x_32 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_33 = lean_usize_to_nat(x_32);
x_34 = lean_mk_empty_array_with_capacity(x_33);
lean_dec(x_33);
lean_inc(x_34);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_36, 2, x_24);
lean_ctor_set(x_36, 3, x_24);
lean_ctor_set_usize(x_36, 4, x_29);
lean_inc(x_23);
x_37 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_37, 0, x_23);
lean_ctor_set(x_37, 1, x_23);
lean_ctor_set(x_37, 2, x_26);
lean_ctor_set(x_37, 3, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_25);
lean_ctor_set(x_38, 1, x_37);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_39 = l_Lean_Meta_simpAll(x_20, x_17, x_18, x_38, x_9, x_10, x_11, x_12, x_21);
lean_dec(x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
x_43 = !lean_is_exclusive(x_40);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_44 = lean_ctor_get(x_40, 0);
x_45 = lean_ctor_get(x_40, 1);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_free_object(x_40);
x_66 = lean_box(0);
x_67 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_66, x_6, x_9, x_10, x_11, x_12, x_41);
lean_dec(x_6);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_50 = x_9;
x_51 = x_10;
x_52 = x_11;
x_53 = x_12;
x_54 = x_68;
goto block_65;
}
else
{
uint8_t x_69; 
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_67);
if (x_69 == 0)
{
return x_67;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_67, 0);
x_71 = lean_ctor_get(x_67, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_67);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_44, 0);
lean_inc(x_73);
lean_dec(x_44);
x_74 = lean_box(0);
lean_ctor_set_tag(x_40, 1);
lean_ctor_set(x_40, 1, x_74);
lean_ctor_set(x_40, 0, x_73);
x_75 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_40, x_6, x_9, x_10, x_11, x_12, x_41);
lean_dec(x_6);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_50 = x_9;
x_51 = x_10;
x_52 = x_11;
x_53 = x_12;
x_54 = x_76;
goto block_65;
}
else
{
uint8_t x_77; 
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_75);
if (x_77 == 0)
{
return x_75;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_75, 0);
x_79 = lean_ctor_get(x_75, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_75);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
block_49:
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
if (lean_is_scalar(x_42)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_42;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
block_65:
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = lean_ctor_get(x_52, 2);
lean_inc(x_55);
x_56 = l_Lean_Elab_Tactic_tactic_simp_trace;
x_57 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_55, x_56);
lean_dec(x_55);
if (x_57 == 0)
{
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_1);
x_46 = x_54;
goto block_49;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_45, 0);
lean_inc(x_58);
x_59 = l_Lean_Elab_Tactic_traceSimpCall(x_1, x_58, x_50, x_51, x_52, x_53, x_54);
lean_dec(x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_46 = x_60;
goto block_49;
}
else
{
uint8_t x_61; 
lean_dec(x_45);
lean_dec(x_42);
x_61 = !lean_is_exclusive(x_59);
if (x_61 == 0)
{
return x_59;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_59, 0);
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_59);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_81 = lean_ctor_get(x_40, 0);
x_82 = lean_ctor_get(x_40, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_40);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_box(0);
x_104 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_103, x_6, x_9, x_10, x_11, x_12, x_41);
lean_dec(x_6);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
x_87 = x_9;
x_88 = x_10;
x_89 = x_11;
x_90 = x_12;
x_91 = x_105;
goto block_102;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_82);
lean_dec(x_42);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_106 = lean_ctor_get(x_104, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_104, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_108 = x_104;
} else {
 lean_dec_ref(x_104);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_81, 0);
lean_inc(x_110);
lean_dec(x_81);
x_111 = lean_box(0);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_112, x_6, x_9, x_10, x_11, x_12, x_41);
lean_dec(x_6);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
lean_dec(x_113);
x_87 = x_9;
x_88 = x_10;
x_89 = x_11;
x_90 = x_12;
x_91 = x_114;
goto block_102;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_82);
lean_dec(x_42);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_115 = lean_ctor_get(x_113, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_117 = x_113;
} else {
 lean_dec_ref(x_113);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
block_86:
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
if (lean_is_scalar(x_42)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_42;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
block_102:
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_92 = lean_ctor_get(x_89, 2);
lean_inc(x_92);
x_93 = l_Lean_Elab_Tactic_tactic_simp_trace;
x_94 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_92, x_93);
lean_dec(x_92);
if (x_94 == 0)
{
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_1);
x_83 = x_91;
goto block_86;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_82, 0);
lean_inc(x_95);
x_96 = l_Lean_Elab_Tactic_traceSimpCall(x_1, x_95, x_87, x_88, x_89, x_90, x_91);
lean_dec(x_95);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_83 = x_97;
goto block_86;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_82);
lean_dec(x_42);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_100 = x_96;
} else {
 lean_dec_ref(x_96);
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
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_119 = !lean_is_exclusive(x_39);
if (x_119 == 0)
{
return x_39;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_39, 0);
x_121 = lean_ctor_get(x_39, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_39);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_123 = !lean_is_exclusive(x_19);
if (x_123 == 0)
{
return x_19;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_19, 0);
x_125 = lean_ctor_get(x_19, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_19);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_127 = !lean_is_exclusive(x_14);
if (x_127 == 0)
{
return x_14;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_14, 0);
x_129 = lean_ctor_get(x_14, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_14);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAll(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_box(1);
x_12 = lean_box(1);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_getSimpTheorems___boxed), 3, 0);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAll___lam__0___boxed), 13, 4);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics), 10, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = l_Lean_Elab_Tactic_withMainContext___redArg(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAll___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = l_Lean_Elab_Tactic_evalSimpAll___lam__0(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAll___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalSimpAll(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAll__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("simpAll", 7, 7);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("evalSimpAll", 11, 11);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAll___boxed), 10, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("evalSimpAll", 11, 11);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(440u);
x_8 = lean_unsigned_to_nat(45u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(448u);
x_11 = lean_unsigned_to_nat(19u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(49u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(60u);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_addBuiltinDeclarationRanges(x_6, x_19, x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_go___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_traceSimpCall(x_1, x_2, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_go___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_getMainGoal(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; lean_object* x_25; lean_object* x_26; size_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_17);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_unsigned_to_nat(0u);
lean_inc(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_17);
x_22 = lean_unsigned_to_nat(2u);
x_23 = lean_unsigned_to_nat(5u);
x_24 = lean_usize_of_nat(x_23);
x_25 = lean_usize_to_nat(x_24);
x_26 = lean_nat_pow(x_22, x_25);
lean_dec(x_25);
x_27 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_28 = lean_usize_to_nat(x_27);
x_29 = lean_mk_empty_array_with_capacity(x_28);
lean_dec(x_28);
lean_inc(x_29);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 2, x_19);
lean_ctor_set(x_31, 3, x_19);
lean_ctor_set_usize(x_31, 4, x_24);
lean_inc(x_18);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_18);
lean_ctor_set(x_32, 1, x_18);
lean_ctor_set(x_32, 2, x_21);
lean_ctor_set(x_32, 3, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_20);
lean_ctor_set(x_33, 1, x_32);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_15);
x_34 = l_Lean_Meta_dsimpGoal(x_15, x_1, x_2, x_3, x_4, x_33, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_37 = x_34;
} else {
 lean_dec_ref(x_34);
 x_37 = lean_box(0);
}
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_39 = lean_ctor_get(x_35, 0);
x_40 = lean_ctor_get(x_35, 1);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_free_object(x_35);
x_67 = lean_box(0);
x_68 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_67, x_6, x_9, x_10, x_11, x_12, x_36);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_45 = x_5;
x_46 = x_6;
x_47 = x_7;
x_48 = x_8;
x_49 = x_9;
x_50 = x_10;
x_51 = x_11;
x_52 = x_12;
x_53 = x_69;
goto block_66;
}
else
{
uint8_t x_70; 
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_70 = !lean_is_exclusive(x_68);
if (x_70 == 0)
{
return x_68;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_68, 0);
x_72 = lean_ctor_get(x_68, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_68);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_39, 0);
lean_inc(x_74);
lean_dec(x_39);
x_75 = lean_box(0);
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 1, x_75);
lean_ctor_set(x_35, 0, x_74);
x_76 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_35, x_6, x_9, x_10, x_11, x_12, x_36);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_45 = x_5;
x_46 = x_6;
x_47 = x_7;
x_48 = x_8;
x_49 = x_9;
x_50 = x_10;
x_51 = x_11;
x_52 = x_12;
x_53 = x_77;
goto block_66;
}
else
{
uint8_t x_78; 
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_78 = !lean_is_exclusive(x_76);
if (x_78 == 0)
{
return x_76;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_76, 0);
x_80 = lean_ctor_get(x_76, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_76);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
block_44:
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
if (lean_is_scalar(x_37)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_37;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
block_66:
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_ctor_get(x_51, 2);
lean_inc(x_54);
x_55 = l_Lean_Elab_Tactic_tactic_simp_trace;
x_56 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_54, x_55);
lean_dec(x_54);
if (x_56 == 0)
{
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_15);
x_41 = x_53;
goto block_44;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_51, 5);
lean_inc(x_57);
x_58 = lean_ctor_get(x_40, 0);
lean_inc(x_58);
x_59 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_go___lam__0___boxed), 11, 2);
lean_closure_set(x_59, 0, x_57);
lean_closure_set(x_59, 1, x_58);
x_60 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_withMainContext_spec__0___redArg(x_15, x_59, x_45, x_46, x_47, x_48, x_49, x_50, x_51, x_52, x_53);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_41 = x_61;
goto block_44;
}
else
{
uint8_t x_62; 
lean_dec(x_40);
lean_dec(x_37);
x_62 = !lean_is_exclusive(x_60);
if (x_62 == 0)
{
return x_60;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_60, 0);
x_64 = lean_ctor_get(x_60, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_60);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_82 = lean_ctor_get(x_35, 0);
x_83 = lean_ctor_get(x_35, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_35);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_box(0);
x_111 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_110, x_6, x_9, x_10, x_11, x_12, x_36);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
x_88 = x_5;
x_89 = x_6;
x_90 = x_7;
x_91 = x_8;
x_92 = x_9;
x_93 = x_10;
x_94 = x_11;
x_95 = x_12;
x_96 = x_112;
goto block_109;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_83);
lean_dec(x_37);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_113 = lean_ctor_get(x_111, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_111, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_115 = x_111;
} else {
 lean_dec_ref(x_111);
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
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_82, 0);
lean_inc(x_117);
lean_dec(x_82);
x_118 = lean_box(0);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_119, x_6, x_9, x_10, x_11, x_12, x_36);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
lean_dec(x_120);
x_88 = x_5;
x_89 = x_6;
x_90 = x_7;
x_91 = x_8;
x_92 = x_9;
x_93 = x_10;
x_94 = x_11;
x_95 = x_12;
x_96 = x_121;
goto block_109;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_83);
lean_dec(x_37);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_122 = lean_ctor_get(x_120, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_124 = x_120;
} else {
 lean_dec_ref(x_120);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
}
block_87:
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
if (lean_is_scalar(x_37)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_37;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
block_109:
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_97 = lean_ctor_get(x_94, 2);
lean_inc(x_97);
x_98 = l_Lean_Elab_Tactic_tactic_simp_trace;
x_99 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_97, x_98);
lean_dec(x_97);
if (x_99 == 0)
{
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_15);
x_84 = x_96;
goto block_87;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_94, 5);
lean_inc(x_100);
x_101 = lean_ctor_get(x_83, 0);
lean_inc(x_101);
x_102 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_go___lam__0___boxed), 11, 2);
lean_closure_set(x_102, 0, x_100);
lean_closure_set(x_102, 1, x_101);
x_103 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_withMainContext_spec__0___redArg(x_15, x_102, x_88, x_89, x_90, x_91, x_92, x_93, x_94, x_95, x_96);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
x_84 = x_104;
goto block_87;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_83);
lean_dec(x_37);
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_107 = x_103;
} else {
 lean_dec_ref(x_103);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_126 = !lean_is_exclusive(x_34);
if (x_126 == 0)
{
return x_34;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_34, 0);
x_128 = lean_ctor_get(x_34, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_34);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
else
{
uint8_t x_130; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_130 = !lean_is_exclusive(x_14);
if (x_130 == 0)
{
return x_14;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_14, 0);
x_132 = lean_ctor_get(x_14, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_14);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_box(x_4);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_go___lam__1___boxed), 13, 4);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_14);
lean_closure_set(x_15, 3, x_3);
x_16 = l_Lean_Elab_Tactic_withSimpDiagnostics(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_go___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_dsimpLocation_go___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_go___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_Elab_Tactic_dsimpLocation_go___lam__1(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l_Lean_Elab_Tactic_dsimpLocation_go(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_15 = l_Lean_MVarId_getNondepPropHyps(x_13, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(1);
x_19 = lean_unbox(x_18);
x_20 = l_Lean_Elab_Tactic_dsimpLocation_go(x_1, x_2, x_16, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
return x_20;
}
else
{
uint8_t x_21; 
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
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
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
x_25 = !lean_is_exclusive(x_12);
if (x_25 == 0)
{
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_12);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_Elab_Tactic_getFVarIds(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_Tactic_dsimpLocation_go(x_2, x_3, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation___lam__0), 11, 2);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
x_14 = l_Lean_Elab_Tactic_withMainContext___redArg(x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
lean_dec(x_3);
x_17 = lean_box(x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation___lam__1___boxed), 13, 4);
lean_closure_set(x_18, 0, x_15);
lean_closure_set(x_18, 1, x_1);
lean_closure_set(x_18, 2, x_2);
lean_closure_set(x_18, 3, x_17);
x_19 = l_Lean_Elab_Tactic_withMainContext___redArg(x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l_Lean_Elab_Tactic_dsimpLocation___lam__1(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_dsimpLocation(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_box(0);
x_12 = lean_box(2);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_getSimpTheorems___boxed), 3, 0);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_11);
lean_closure_set(x_14, 4, x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_15 = l_Lean_Elab_Tactic_withMainContext___redArg(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_unsigned_to_nat(5u);
x_21 = l_Lean_Syntax_getArg(x_1, x_20);
lean_dec(x_1);
x_22 = l_Lean_Elab_Tactic_expandOptLocation(x_21);
lean_dec(x_21);
x_23 = l_Lean_Elab_Tactic_dsimpLocation(x_18, x_19, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalDSimp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimp__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("dsimp", 5, 5);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("evalDSimp", 9, 9);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimp___boxed), 10, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("evalDSimp", 9, 9);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(470u);
x_8 = lean_unsigned_to_nat(43u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(472u);
x_11 = lean_unsigned_to_nat(55u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(47u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(56u);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_addBuiltinDeclarationRanges(x_6, x_19, x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_getSimpArgs_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("simpArgs", 8, 8);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
lean_inc(x_1);
x_7 = l_Lean_Syntax_isOfKind(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
lean_dec(x_1);
x_11 = l_Lean_Syntax_getArgs(x_10);
lean_dec(x_10);
x_12 = l_Lean_Syntax_TSepArray_getElems___redArg(x_11);
lean_dec(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_getDSimpArgs_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("dsimpArgs", 9, 9);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
lean_inc(x_1);
x_7 = l_Lean_Syntax_isOfKind(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
lean_dec(x_1);
x_11 = l_Lean_Syntax_getArgs(x_10);
lean_dec(x_10);
x_12 = l_Lean_Syntax_TSepArray_getElems___redArg(x_11);
lean_dec(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
lean_object* initialize_Lean_Meta_Tactic_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Replace(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_BuiltinNotation(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Location(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Config(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Simp(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Replace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_BuiltinNotation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_ElabTerm(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Location(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Config(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_instInhabitedSimpKind = _init_l_Lean_Elab_Tactic_instInhabitedSimpKind();
l_Lean_Elab_Tactic_instBEqSimpKind = _init_l_Lean_Elab_Tactic_instBEqSimpKind();
lean_mark_persistent(l_Lean_Elab_Tactic_instBEqSimpKind);
l_Lean_Elab_Tactic_simpParamsPos = _init_l_Lean_Elab_Tactic_simpParamsPos();
lean_mark_persistent(l_Lean_Elab_Tactic_simpParamsPos);
l_Lean_Elab_Tactic_simpOnlyPos = _init_l_Lean_Elab_Tactic_simpOnlyPos();
lean_mark_persistent(l_Lean_Elab_Tactic_simpOnlyPos);
l_Lean_Elab_Tactic_simpOnlyBuiltins = _init_l_Lean_Elab_Tactic_simpOnlyBuiltins();
lean_mark_persistent(l_Lean_Elab_Tactic_simpOnlyBuiltins);
if (builtin) {res = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_7019_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_tactic_simp_trace = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_tactic_simp_trace);
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalSimp__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalSimpAll__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalDSimp__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
