// Lean compiler output
// Module: Lean.Elab.Tactic.Simpa
// Imports: Lean.Meta.Tactic.Assumption Lean.Meta.Tactic.TryThis Lean.Elab.Tactic.Simp Lean.Elab.App Lean.Linter.Basic
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
LEAN_EXPORT lean_object* l_linter_unnecessarySimpa;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(lean_object*);
lean_object* l_Lean_Meta_getSimpTheorems___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__8___boxed(lean_object**);
extern lean_object* l_Lean_Elab_Tactic_tactic_simp_trace;
lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_withMainContext_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at___Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_getRoundtrippingUserName_x3f(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpGoal(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_filterOldMVars___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3026_(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assign___at___Lean_Elab_Tactic_refineCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_focus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___boxed(lean_object**);
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Array_mkArray2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___boxed(lean_object**);
lean_object* l_Lean_Meta_Simp_Context_setFailIfUnchanged(lean_object*, uint8_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_Elab_Tactic_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51_(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_instReprUseImplicitLambdaResult;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1(lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_instInhabitedTacticM(lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withSimpDiagnostics(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_note(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectFVars_visit_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getExprAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assumption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_Elab_Tactic_mkSimpContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Elab_Tactic_closeMainGoal___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwTypeMismatchError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_logUnassignedAndAbort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___boxed(lean_object**);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Context_setAutoUnfold(lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___boxed(lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectFVars_visit_spec__1___redArg(lean_object*);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_unsetTrailing(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_rename(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_setGoals___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkSimpOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_mkArray3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_logAt___at___Lean_logErrorAt___at___Lean_Elab_logException___at___Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
LEAN_EXPORT lean_object* l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("linter", 6, 6);
x_3 = lean_mk_string_unchecked("unnecessarySimpa", 16, 16);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_mk_string_unchecked("", 0, 0);
x_7 = lean_mk_string_unchecked("enable the 'unnecessary simpa' linter", 37, 37);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
lean_inc(x_4);
x_9 = l_Lean_Option_register___at___Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6__spec__0(x_4, x_8, x_4, x_1);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_linter_unnecessarySimpa;
x_3 = l_Lean_Linter_getLinterValue(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_12; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_unsigned_to_nat(1024u);
x_22 = lean_nat_dec_le(x_21, x_2);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_unsigned_to_nat(2u);
x_24 = lean_nat_to_int(x_23);
x_3 = x_24;
goto block_11;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_to_int(x_25);
x_3 = x_26;
goto block_11;
}
}
case 1:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_43; uint8_t x_44; 
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_28 = x_1;
} else {
 lean_dec_ref(x_1);
 x_28 = lean_box(0);
}
x_43 = lean_unsigned_to_nat(1024u);
x_44 = lean_nat_dec_le(x_43, x_2);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_unsigned_to_nat(2u);
x_46 = lean_nat_to_int(x_45);
x_29 = x_46;
goto block_42;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_to_int(x_47);
x_29 = x_48;
goto block_42;
}
block_42:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_30 = lean_mk_string_unchecked("Lean.Elab.Term.UseImplicitLambdaResult.yes", 42, 42);
if (lean_is_scalar(x_28)) {
 x_31 = lean_alloc_ctor(3, 1, 0);
} else {
 x_31 = x_28;
 lean_ctor_set_tag(x_31, 3);
}
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_box(1);
x_33 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_unsigned_to_nat(1024u);
x_35 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3026_(x_27, x_34);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_39, 0, x_37);
x_40 = lean_unbox(x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_40);
x_41 = l_Repr_addAppParen(x_39, x_2);
return x_41;
}
}
default: 
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_unsigned_to_nat(1024u);
x_50 = lean_nat_dec_le(x_49, x_2);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_unsigned_to_nat(2u);
x_52 = lean_nat_to_int(x_51);
x_12 = x_52;
goto block_20;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_to_int(x_53);
x_12 = x_54;
goto block_20;
}
}
}
block_11:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_4 = lean_mk_string_unchecked("Lean.Elab.Term.UseImplicitLambdaResult.no", 41, 41);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_9);
x_10 = l_Repr_addAppParen(x_8, x_2);
return x_10;
}
block_20:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_13 = lean_mk_string_unchecked("Lean.Elab.Term.UseImplicitLambdaResult.postpone", 47, 47);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_17, 0, x_15);
x_18 = lean_unbox(x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_18);
x_19 = l_Repr_addAppParen(x_17, x_2);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_instReprUseImplicitLambdaResult() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Elab_Tactic_instInhabitedTacticM(lean_box(0));
x_12 = lean_panic_fn(x_11, x_1);
x_13 = lean_apply_9(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_box(1);
x_9 = lean_box(0);
x_10 = lean_unbox(x_8);
x_11 = lean_unbox(x_9);
x_12 = l_Lean_logAt___at___Lean_logErrorAt___at___Lean_Elab_logException___at___Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_10, x_11, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___redArg(x_1, x_2, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_13 = lean_mk_string_unchecked("note: this linter can be disabled with `set_option ", 51, 51);
x_14 = l_Lean_stringToMessageData(x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
lean_inc(x_15);
x_16 = l_Lean_MessageData_ofName(x_15);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_mk_string_unchecked(" false`", 7, 7);
x_19 = l_Lean_stringToMessageData(x_18);
lean_dec(x_18);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_mk_string_unchecked("", 0, 0);
x_22 = l_Lean_stringToMessageData(x_21);
lean_dec(x_21);
lean_inc(x_22);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_3);
x_24 = lean_mk_string_unchecked("\n", 1, 1);
x_25 = l_Lean_stringToMessageData(x_24);
lean_dec(x_24);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_20);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_22);
x_29 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_29, 0, x_15);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___redArg(x_2, x_29, x_8, x_9, x_10, x_11, x_12);
return x_30;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_9 = l_Lean_MetavarContext_getExprAssignmentCore_x3f(x_8, x_1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
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
x_15 = l_Lean_MetavarContext_getExprAssignmentCore_x3f(x_14, x_1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_getExprMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3_spec__3___redArg(x_1, x_2, x_8, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_9 = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(x_8, x_1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
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
x_15 = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(x_14, x_1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_getDelayedMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3_spec__4___redArg(x_1, x_2, x_8, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_name_eq(x_1, x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = l_Lean_getExprMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3_spec__3___redArg(x_2, x_3, x_9, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = l_Lean_getDelayedMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3_spec__4___redArg(x_2, x_19, x_9, x_18);
lean_dec(x_2);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_20, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_21);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_21, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_22, 0, x_29);
return x_20;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_dec(x_21);
x_31 = lean_box(0);
lean_ctor_set(x_22, 0, x_31);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_22);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_20, 0, x_32);
return x_20;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_20, 1);
lean_inc(x_33);
lean_dec(x_20);
x_34 = lean_ctor_get(x_21, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_35 = x_21;
} else {
 lean_dec_ref(x_21);
 x_35 = lean_box(0);
}
x_36 = lean_box(0);
lean_ctor_set(x_22, 0, x_36);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_22);
lean_ctor_set(x_37, 1, x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_free_object(x_22);
x_39 = lean_ctor_get(x_20, 1);
lean_inc(x_39);
lean_dec(x_20);
x_40 = lean_ctor_get(x_21, 1);
lean_inc(x_40);
lean_dec(x_21);
x_41 = lean_ctor_get(x_24, 0);
lean_inc(x_41);
lean_dec(x_24);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_2 = x_42;
x_3 = x_40;
x_12 = x_39;
goto _start;
}
}
else
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_22, 0);
lean_inc(x_44);
lean_dec(x_22);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_45 = lean_ctor_get(x_20, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_46 = x_20;
} else {
 lean_dec_ref(x_20);
 x_46 = lean_box(0);
}
x_47 = lean_ctor_get(x_21, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_48 = x_21;
} else {
 lean_dec_ref(x_21);
 x_48 = lean_box(0);
}
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
if (lean_is_scalar(x_48)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_48;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
if (lean_is_scalar(x_46)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_46;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_45);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_20, 1);
lean_inc(x_53);
lean_dec(x_20);
x_54 = lean_ctor_get(x_21, 1);
lean_inc(x_54);
lean_dec(x_21);
x_55 = lean_ctor_get(x_44, 0);
lean_inc(x_55);
lean_dec(x_44);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_2 = x_56;
x_3 = x_54;
x_12 = x_53;
goto _start;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_2);
x_58 = lean_ctor_get(x_14, 1);
lean_inc(x_58);
lean_dec(x_14);
x_59 = lean_ctor_get(x_15, 1);
lean_inc(x_59);
lean_dec(x_15);
x_60 = lean_ctor_get(x_17, 0);
lean_inc(x_60);
lean_dec(x_17);
x_61 = l_Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3(x_1, x_60, x_59, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_58);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_2);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_3);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_12);
return x_65;
}
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l_Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3(x_1, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_4);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l_Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3(x_1, x_4, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_19);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = l_Lean_Expr_hasExprMVar(x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint64_t x_21; lean_object* x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; lean_object* x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; size_t x_30; size_t x_31; lean_object* x_32; size_t x_33; size_t x_34; size_t x_35; lean_object* x_36; uint8_t x_37; 
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
x_20 = lean_array_get_size(x_19);
x_21 = l_Lean_Expr_hash(x_2);
x_22 = lean_unsigned_to_nat(32u);
x_23 = lean_uint64_of_nat(x_22);
x_24 = lean_uint64_shift_right(x_21, x_23);
x_25 = lean_uint64_xor(x_21, x_24);
x_26 = lean_unsigned_to_nat(16u);
x_27 = lean_uint64_of_nat(x_26);
x_28 = lean_uint64_shift_right(x_25, x_27);
x_29 = lean_uint64_xor(x_25, x_28);
x_30 = lean_uint64_to_usize(x_29);
x_31 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_usize_of_nat(x_32);
x_34 = lean_usize_sub(x_31, x_33);
x_35 = lean_usize_land(x_30, x_34);
x_36 = lean_array_uget(x_19, x_35);
x_37 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectFVars_visit_spec__0(lean_box(0), x_2, x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_box(0);
if (x_37 == 0)
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_3);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_83 = lean_ctor_get(x_3, 1);
lean_dec(x_83);
x_84 = lean_ctor_get(x_3, 0);
lean_dec(x_84);
x_85 = lean_nat_add(x_18, x_32);
lean_dec(x_18);
lean_inc(x_2);
x_86 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_86, 0, x_2);
lean_ctor_set(x_86, 1, x_38);
lean_ctor_set(x_86, 2, x_36);
x_87 = lean_array_uset(x_19, x_35, x_86);
x_88 = lean_unsigned_to_nat(2u);
x_89 = lean_nat_shiftl(x_85, x_88);
x_90 = lean_unsigned_to_nat(3u);
x_91 = lean_nat_div(x_89, x_90);
lean_dec(x_89);
x_92 = lean_array_get_size(x_87);
x_93 = lean_nat_dec_le(x_91, x_92);
lean_dec(x_92);
lean_dec(x_91);
if (x_93 == 0)
{
lean_object* x_94; 
x_94 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectFVars_visit_spec__1___redArg(x_87);
lean_ctor_set(x_3, 1, x_94);
lean_ctor_set(x_3, 0, x_85);
x_39 = x_3;
goto block_81;
}
else
{
lean_ctor_set(x_3, 1, x_87);
lean_ctor_set(x_3, 0, x_85);
x_39 = x_3;
goto block_81;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
lean_dec(x_3);
x_95 = lean_nat_add(x_18, x_32);
lean_dec(x_18);
lean_inc(x_2);
x_96 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_96, 0, x_2);
lean_ctor_set(x_96, 1, x_38);
lean_ctor_set(x_96, 2, x_36);
x_97 = lean_array_uset(x_19, x_35, x_96);
x_98 = lean_unsigned_to_nat(2u);
x_99 = lean_nat_shiftl(x_95, x_98);
x_100 = lean_unsigned_to_nat(3u);
x_101 = lean_nat_div(x_99, x_100);
lean_dec(x_99);
x_102 = lean_array_get_size(x_97);
x_103 = lean_nat_dec_le(x_101, x_102);
lean_dec(x_102);
lean_dec(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectFVars_visit_spec__1___redArg(x_97);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_95);
lean_ctor_set(x_105, 1, x_104);
x_39 = x_105;
goto block_81;
}
else
{
lean_object* x_106; 
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_95);
lean_ctor_set(x_106, 1, x_97);
x_39 = x_106;
goto block_81;
}
}
}
else
{
lean_dec(x_36);
lean_dec(x_19);
lean_dec(x_18);
x_39 = x_3;
goto block_81;
}
block_81:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_2, 0);
lean_inc(x_40);
lean_dec(x_2);
x_41 = l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3(x_1, x_40, x_39, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_41;
}
case 5:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_2, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_2, 1);
lean_inc(x_43);
lean_dec(x_2);
x_44 = l_Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3(x_1, x_42, x_39, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_43);
return x_44;
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_46);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_2 = x_43;
x_3 = x_48;
x_12 = x_47;
goto _start;
}
}
case 6:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_2, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_2, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_2, 2);
lean_inc(x_52);
x_53 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
x_54 = l_Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3___lam__0(x_1, x_50, x_51, x_52, x_53, x_39, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_50);
return x_54;
}
case 7:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_2, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_2, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_2, 2);
lean_inc(x_57);
x_58 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
x_59 = l_Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3___lam__0(x_1, x_55, x_56, x_57, x_58, x_39, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_55);
return x_59;
}
case 8:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_2, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_2, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_2, 3);
lean_inc(x_62);
lean_dec(x_2);
x_63 = l_Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3(x_1, x_60, x_39, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
return x_63;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_68 = l_Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3(x_1, x_61, x_67, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_66);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_obj_tag(x_70) == 0)
{
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_62);
return x_68;
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_70);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_2 = x_62;
x_3 = x_72;
x_12 = x_71;
goto _start;
}
}
}
case 10:
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_2, 1);
lean_inc(x_74);
lean_dec(x_2);
x_2 = x_74;
x_3 = x_39;
goto _start;
}
case 11:
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_2, 2);
lean_inc(x_76);
lean_dec(x_2);
x_2 = x_76;
x_3 = x_39;
goto _start;
}
default: 
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_2);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_38);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_39);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_12);
return x_80;
}
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_36);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_2);
x_107 = lean_box(0);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_3);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_12);
return x_110;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = l_Lean_Expr_hasExprMVar(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_13 = lean_box(1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_15 = lean_unsigned_to_nat(8u);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_nat_shiftl(x_15, x_17);
x_19 = lean_unsigned_to_nat(3u);
x_20 = lean_nat_div(x_18, x_19);
lean_dec(x_18);
x_21 = l_Nat_nextPowerOfTwo(x_20);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = lean_mk_array(x_21, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3(x_1, x_2, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_25, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_25, 0, x_30);
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_27);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_25, 0);
lean_dec(x_35);
x_36 = lean_box(x_12);
lean_ctor_set(x_25, 0, x_36);
return x_25;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_dec(x_25);
x_38 = lean_box(x_12);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_7, 5);
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
x_13 = l_Lean_SourceInfo_fromRef(x_10, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_13 = lean_ctor_get(x_10, 5);
lean_inc(x_13);
x_14 = lean_mk_string_unchecked("tactic", 6, 6);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
x_17 = lean_box(0);
x_18 = lean_box(0);
x_19 = lean_box(0);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_17);
lean_ctor_set(x_21, 3, x_18);
lean_ctor_set(x_21, 4, x_19);
lean_ctor_set(x_21, 5, x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_13);
x_23 = lean_mk_string_unchecked("Try this: ", 10, 10);
lean_inc(x_11);
lean_inc(x_10);
x_24 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_1, x_21, x_22, x_23, x_17, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_apply_10(x_2, x_25, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_26);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_24);
if (x_28 == 0)
{
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 0);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_24);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, uint8_t x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29, lean_object* x_30, lean_object* x_31, lean_object* x_32, lean_object* x_33) {
_start:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_378; uint8_t x_448; lean_object* x_452; lean_object* x_453; uint8_t x_454; 
lean_inc(x_24);
x_34 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__1___boxed), 11, 1);
lean_closure_set(x_34, 0, x_24);
x_452 = lean_ctor_get(x_31, 2);
lean_inc(x_452);
x_453 = l_Lean_Elab_Tactic_tactic_simp_trace;
x_454 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_452, x_453);
lean_dec(x_452);
if (x_454 == 0)
{
if (lean_obj_tag(x_22) == 0)
{
x_448 = x_454;
goto block_451;
}
else
{
x_448 = x_23;
goto block_451;
}
}
else
{
goto block_447;
}
block_57:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = l_Array_append(lean_box(0), x_2, x_51);
lean_dec(x_51);
lean_inc(x_48);
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_3);
lean_ctor_set(x_53, 2, x_52);
lean_inc(x_48);
x_54 = l_Lean_Syntax_node5(x_48, x_4, x_37, x_45, x_46, x_39, x_53);
lean_inc(x_40);
x_55 = l_Lean_Syntax_node4(x_48, x_9, x_38, x_40, x_40, x_54);
x_56 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2(x_1, x_34, x_55, x_41, x_36, x_44, x_49, x_47, x_50, x_43, x_42, x_35);
return x_56;
}
block_82:
{
lean_object* x_75; lean_object* x_76; 
lean_inc(x_2);
x_75 = l_Array_append(lean_box(0), x_2, x_74);
lean_dec(x_74);
lean_inc(x_3);
lean_inc(x_71);
x_76 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_76, 0, x_71);
lean_ctor_set(x_76, 1, x_3);
lean_ctor_set(x_76, 2, x_75);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_77; 
x_77 = l_Array_empty(lean_box(0));
x_35 = x_58;
x_36 = x_59;
x_37 = x_60;
x_38 = x_61;
x_39 = x_76;
x_40 = x_62;
x_41 = x_63;
x_42 = x_64;
x_43 = x_65;
x_44 = x_67;
x_45 = x_68;
x_46 = x_69;
x_47 = x_70;
x_48 = x_71;
x_49 = x_72;
x_50 = x_73;
x_51 = x_77;
goto block_57;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_66, 0);
lean_inc(x_78);
lean_dec(x_66);
x_79 = lean_mk_string_unchecked("using", 5, 5);
lean_inc(x_71);
x_80 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_80, 0, x_71);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Array_mkArray2(lean_box(0), x_80, x_78);
x_35 = x_58;
x_36 = x_59;
x_37 = x_60;
x_38 = x_61;
x_39 = x_76;
x_40 = x_62;
x_41 = x_63;
x_42 = x_64;
x_43 = x_65;
x_44 = x_67;
x_45 = x_68;
x_46 = x_69;
x_47 = x_70;
x_48 = x_71;
x_49 = x_72;
x_50 = x_73;
x_51 = x_81;
goto block_57;
}
}
block_114:
{
lean_object* x_100; lean_object* x_101; 
lean_inc(x_2);
x_100 = l_Array_append(lean_box(0), x_2, x_99);
lean_dec(x_99);
lean_inc(x_3);
lean_inc(x_95);
x_101 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_101, 0, x_95);
lean_ctor_set(x_101, 1, x_3);
lean_ctor_set(x_101, 2, x_100);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_102; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_102 = l_Array_empty(lean_box(0));
x_58 = x_83;
x_59 = x_84;
x_60 = x_85;
x_61 = x_86;
x_62 = x_87;
x_63 = x_88;
x_64 = x_89;
x_65 = x_90;
x_66 = x_91;
x_67 = x_92;
x_68 = x_93;
x_69 = x_101;
x_70 = x_94;
x_71 = x_95;
x_72 = x_97;
x_73 = x_98;
x_74 = x_102;
goto block_82;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_103 = lean_ctor_get(x_96, 0);
lean_inc(x_103);
lean_dec(x_96);
x_104 = lean_mk_string_unchecked("simpArgs", 8, 8);
x_105 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_104);
x_106 = lean_mk_string_unchecked("[", 1, 1);
lean_inc(x_95);
x_107 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_107, 0, x_95);
lean_ctor_set(x_107, 1, x_106);
lean_inc(x_2);
x_108 = l_Array_append(lean_box(0), x_2, x_103);
lean_dec(x_103);
lean_inc(x_3);
lean_inc(x_95);
x_109 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_109, 0, x_95);
lean_ctor_set(x_109, 1, x_3);
lean_ctor_set(x_109, 2, x_108);
x_110 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_95);
x_111 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_111, 0, x_95);
lean_ctor_set(x_111, 1, x_110);
lean_inc(x_95);
x_112 = l_Lean_Syntax_node3(x_95, x_105, x_107, x_109, x_111);
x_113 = l_Array_mkArray1___redArg(x_112);
x_58 = x_83;
x_59 = x_84;
x_60 = x_85;
x_61 = x_86;
x_62 = x_87;
x_63 = x_88;
x_64 = x_89;
x_65 = x_90;
x_66 = x_91;
x_67 = x_92;
x_68 = x_93;
x_69 = x_101;
x_70 = x_94;
x_71 = x_95;
x_72 = x_97;
x_73 = x_98;
x_74 = x_113;
goto block_82;
}
}
block_140:
{
lean_object* x_132; lean_object* x_133; 
lean_inc(x_2);
x_132 = l_Array_append(lean_box(0), x_2, x_131);
lean_dec(x_131);
lean_inc(x_3);
lean_inc(x_127);
x_133 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_133, 0, x_127);
lean_ctor_set(x_133, 1, x_3);
lean_ctor_set(x_133, 2, x_132);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_134; 
x_134 = l_Array_empty(lean_box(0));
x_83 = x_115;
x_84 = x_116;
x_85 = x_117;
x_86 = x_118;
x_87 = x_119;
x_88 = x_120;
x_89 = x_122;
x_90 = x_123;
x_91 = x_124;
x_92 = x_125;
x_93 = x_133;
x_94 = x_126;
x_95 = x_127;
x_96 = x_128;
x_97 = x_129;
x_98 = x_130;
x_99 = x_134;
goto block_114;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_135 = lean_ctor_get(x_121, 0);
lean_inc(x_135);
lean_dec(x_121);
x_136 = l_Lean_SourceInfo_fromRef(x_135, x_8);
lean_dec(x_135);
x_137 = lean_mk_string_unchecked("only", 4, 4);
x_138 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
x_139 = l_Array_mkArray1___redArg(x_138);
x_83 = x_115;
x_84 = x_116;
x_85 = x_117;
x_86 = x_118;
x_87 = x_119;
x_88 = x_120;
x_89 = x_122;
x_90 = x_123;
x_91 = x_124;
x_92 = x_125;
x_93 = x_133;
x_94 = x_126;
x_95 = x_127;
x_96 = x_128;
x_97 = x_129;
x_98 = x_130;
x_99 = x_139;
goto block_114;
}
}
block_163:
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_158 = l_Array_append(lean_box(0), x_2, x_157);
lean_dec(x_157);
lean_inc(x_149);
x_159 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_159, 0, x_149);
lean_ctor_set(x_159, 1, x_3);
lean_ctor_set(x_159, 2, x_158);
lean_inc(x_149);
x_160 = l_Lean_Syntax_node5(x_149, x_4, x_143, x_141, x_153, x_147, x_159);
x_161 = l_Lean_Syntax_node2(x_149, x_152, x_150, x_160);
x_162 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2(x_1, x_34, x_161, x_144, x_142, x_148, x_155, x_154, x_156, x_146, x_145, x_151);
return x_162;
}
block_188:
{
lean_object* x_181; lean_object* x_182; 
lean_inc(x_2);
x_181 = l_Array_append(lean_box(0), x_2, x_180);
lean_dec(x_180);
lean_inc(x_3);
lean_inc(x_172);
x_182 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_182, 0, x_172);
lean_ctor_set(x_182, 1, x_3);
lean_ctor_set(x_182, 2, x_181);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_183; 
x_183 = l_Array_empty(lean_box(0));
x_141 = x_164;
x_142 = x_165;
x_143 = x_166;
x_144 = x_167;
x_145 = x_168;
x_146 = x_169;
x_147 = x_182;
x_148 = x_171;
x_149 = x_172;
x_150 = x_173;
x_151 = x_174;
x_152 = x_175;
x_153 = x_176;
x_154 = x_177;
x_155 = x_178;
x_156 = x_179;
x_157 = x_183;
goto block_163;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_184 = lean_ctor_get(x_170, 0);
lean_inc(x_184);
lean_dec(x_170);
x_185 = lean_mk_string_unchecked("using", 5, 5);
lean_inc(x_172);
x_186 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_186, 0, x_172);
lean_ctor_set(x_186, 1, x_185);
x_187 = l_Array_mkArray2(lean_box(0), x_186, x_184);
x_141 = x_164;
x_142 = x_165;
x_143 = x_166;
x_144 = x_167;
x_145 = x_168;
x_146 = x_169;
x_147 = x_182;
x_148 = x_171;
x_149 = x_172;
x_150 = x_173;
x_151 = x_174;
x_152 = x_175;
x_153 = x_176;
x_154 = x_177;
x_155 = x_178;
x_156 = x_179;
x_157 = x_187;
goto block_163;
}
}
block_220:
{
lean_object* x_206; lean_object* x_207; 
lean_inc(x_2);
x_206 = l_Array_append(lean_box(0), x_2, x_205);
lean_dec(x_205);
lean_inc(x_3);
lean_inc(x_197);
x_207 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_207, 0, x_197);
lean_ctor_set(x_207, 1, x_3);
lean_ctor_set(x_207, 2, x_206);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_208; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_208 = l_Array_empty(lean_box(0));
x_164 = x_189;
x_165 = x_190;
x_166 = x_191;
x_167 = x_192;
x_168 = x_193;
x_169 = x_194;
x_170 = x_195;
x_171 = x_196;
x_172 = x_197;
x_173 = x_198;
x_174 = x_199;
x_175 = x_200;
x_176 = x_207;
x_177 = x_201;
x_178 = x_203;
x_179 = x_204;
x_180 = x_208;
goto block_188;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_209 = lean_ctor_get(x_202, 0);
lean_inc(x_209);
lean_dec(x_202);
x_210 = lean_mk_string_unchecked("simpArgs", 8, 8);
x_211 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_210);
x_212 = lean_mk_string_unchecked("[", 1, 1);
lean_inc(x_197);
x_213 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_213, 0, x_197);
lean_ctor_set(x_213, 1, x_212);
lean_inc(x_2);
x_214 = l_Array_append(lean_box(0), x_2, x_209);
lean_dec(x_209);
lean_inc(x_3);
lean_inc(x_197);
x_215 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_215, 0, x_197);
lean_ctor_set(x_215, 1, x_3);
lean_ctor_set(x_215, 2, x_214);
x_216 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_197);
x_217 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_217, 0, x_197);
lean_ctor_set(x_217, 1, x_216);
lean_inc(x_197);
x_218 = l_Lean_Syntax_node3(x_197, x_211, x_213, x_215, x_217);
x_219 = l_Array_mkArray1___redArg(x_218);
x_164 = x_189;
x_165 = x_190;
x_166 = x_191;
x_167 = x_192;
x_168 = x_193;
x_169 = x_194;
x_170 = x_195;
x_171 = x_196;
x_172 = x_197;
x_173 = x_198;
x_174 = x_199;
x_175 = x_200;
x_176 = x_207;
x_177 = x_201;
x_178 = x_203;
x_179 = x_204;
x_180 = x_219;
goto block_188;
}
}
block_246:
{
lean_object* x_238; lean_object* x_239; 
lean_inc(x_2);
x_238 = l_Array_append(lean_box(0), x_2, x_237);
lean_dec(x_237);
lean_inc(x_3);
lean_inc(x_229);
x_239 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_239, 0, x_229);
lean_ctor_set(x_239, 1, x_3);
lean_ctor_set(x_239, 2, x_238);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_240; 
x_240 = l_Array_empty(lean_box(0));
x_189 = x_239;
x_190 = x_221;
x_191 = x_222;
x_192 = x_223;
x_193 = x_225;
x_194 = x_226;
x_195 = x_227;
x_196 = x_228;
x_197 = x_229;
x_198 = x_230;
x_199 = x_231;
x_200 = x_232;
x_201 = x_233;
x_202 = x_234;
x_203 = x_235;
x_204 = x_236;
x_205 = x_240;
goto block_220;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_241 = lean_ctor_get(x_224, 0);
lean_inc(x_241);
lean_dec(x_224);
x_242 = l_Lean_SourceInfo_fromRef(x_241, x_8);
lean_dec(x_241);
x_243 = lean_mk_string_unchecked("only", 4, 4);
x_244 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
x_245 = l_Array_mkArray1___redArg(x_244);
x_189 = x_239;
x_190 = x_221;
x_191 = x_222;
x_192 = x_223;
x_193 = x_225;
x_194 = x_226;
x_195 = x_227;
x_196 = x_228;
x_197 = x_229;
x_198 = x_230;
x_199 = x_231;
x_200 = x_232;
x_201 = x_233;
x_202 = x_234;
x_203 = x_235;
x_204 = x_236;
x_205 = x_245;
goto block_220;
}
}
block_311:
{
if (x_10 == 0)
{
lean_object* x_261; 
lean_inc(x_250);
lean_inc(x_252);
lean_inc(x_259);
lean_inc(x_256);
lean_inc(x_258);
lean_inc(x_253);
lean_inc(x_247);
lean_inc(x_249);
x_261 = lean_apply_9(x_11, x_249, x_247, x_253, x_258, x_256, x_259, x_252, x_250, x_255);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec(x_261);
x_264 = lean_st_ref_get(x_250, x_263);
x_265 = !lean_is_exclusive(x_264);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_266 = lean_ctor_get(x_264, 1);
x_267 = lean_ctor_get(x_264, 0);
lean_dec(x_267);
lean_inc(x_262);
lean_ctor_set_tag(x_264, 2);
lean_ctor_set(x_264, 1, x_12);
lean_ctor_set(x_264, 0, x_262);
lean_inc(x_2);
lean_inc(x_3);
lean_inc(x_262);
x_268 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_268, 0, x_262);
lean_ctor_set(x_268, 1, x_3);
lean_ctor_set(x_268, 2, x_2);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_269; 
x_269 = l_Array_empty(lean_box(0));
x_115 = x_266;
x_116 = x_247;
x_117 = x_248;
x_118 = x_264;
x_119 = x_268;
x_120 = x_249;
x_121 = x_251;
x_122 = x_250;
x_123 = x_252;
x_124 = x_254;
x_125 = x_253;
x_126 = x_256;
x_127 = x_262;
x_128 = x_257;
x_129 = x_258;
x_130 = x_259;
x_131 = x_269;
goto block_140;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_270 = lean_ctor_get(x_260, 0);
lean_inc(x_270);
lean_dec(x_260);
x_271 = l_Array_empty(lean_box(0));
x_272 = lean_array_push(x_271, x_270);
x_115 = x_266;
x_116 = x_247;
x_117 = x_248;
x_118 = x_264;
x_119 = x_268;
x_120 = x_249;
x_121 = x_251;
x_122 = x_250;
x_123 = x_252;
x_124 = x_254;
x_125 = x_253;
x_126 = x_256;
x_127 = x_262;
x_128 = x_257;
x_129 = x_258;
x_130 = x_259;
x_131 = x_272;
goto block_140;
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_273 = lean_ctor_get(x_264, 1);
lean_inc(x_273);
lean_dec(x_264);
lean_inc(x_262);
x_274 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_274, 0, x_262);
lean_ctor_set(x_274, 1, x_12);
lean_inc(x_2);
lean_inc(x_3);
lean_inc(x_262);
x_275 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_275, 0, x_262);
lean_ctor_set(x_275, 1, x_3);
lean_ctor_set(x_275, 2, x_2);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_276; 
x_276 = l_Array_empty(lean_box(0));
x_115 = x_273;
x_116 = x_247;
x_117 = x_248;
x_118 = x_274;
x_119 = x_275;
x_120 = x_249;
x_121 = x_251;
x_122 = x_250;
x_123 = x_252;
x_124 = x_254;
x_125 = x_253;
x_126 = x_256;
x_127 = x_262;
x_128 = x_257;
x_129 = x_258;
x_130 = x_259;
x_131 = x_276;
goto block_140;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_277 = lean_ctor_get(x_260, 0);
lean_inc(x_277);
lean_dec(x_260);
x_278 = l_Array_empty(lean_box(0));
x_279 = lean_array_push(x_278, x_277);
x_115 = x_273;
x_116 = x_247;
x_117 = x_248;
x_118 = x_274;
x_119 = x_275;
x_120 = x_249;
x_121 = x_251;
x_122 = x_250;
x_123 = x_252;
x_124 = x_254;
x_125 = x_253;
x_126 = x_256;
x_127 = x_262;
x_128 = x_257;
x_129 = x_258;
x_130 = x_259;
x_131 = x_279;
goto block_140;
}
}
}
else
{
uint8_t x_280; 
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_254);
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_34);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_280 = !lean_is_exclusive(x_261);
if (x_280 == 0)
{
return x_261;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_281 = lean_ctor_get(x_261, 0);
x_282 = lean_ctor_get(x_261, 1);
lean_inc(x_282);
lean_inc(x_281);
lean_dec(x_261);
x_283 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_283, 0, x_281);
lean_ctor_set(x_283, 1, x_282);
return x_283;
}
}
}
else
{
lean_object* x_284; 
lean_dec(x_12);
lean_dec(x_9);
lean_inc(x_250);
lean_inc(x_252);
lean_inc(x_259);
lean_inc(x_256);
lean_inc(x_258);
lean_inc(x_253);
lean_inc(x_247);
lean_inc(x_249);
x_284 = lean_apply_9(x_11, x_249, x_247, x_253, x_258, x_256, x_259, x_252, x_250, x_255);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; 
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
lean_dec(x_284);
x_287 = lean_st_ref_get(x_250, x_286);
x_288 = !lean_is_exclusive(x_287);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_289 = lean_ctor_get(x_287, 1);
x_290 = lean_ctor_get(x_287, 0);
lean_dec(x_290);
x_291 = lean_mk_string_unchecked("tacticSimpa!_", 13, 13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_292 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_291);
x_293 = lean_mk_string_unchecked("simpa!", 6, 6);
lean_inc(x_285);
lean_ctor_set_tag(x_287, 2);
lean_ctor_set(x_287, 1, x_293);
lean_ctor_set(x_287, 0, x_285);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_294; 
x_294 = l_Array_empty(lean_box(0));
x_221 = x_247;
x_222 = x_248;
x_223 = x_249;
x_224 = x_251;
x_225 = x_250;
x_226 = x_252;
x_227 = x_254;
x_228 = x_253;
x_229 = x_285;
x_230 = x_287;
x_231 = x_289;
x_232 = x_292;
x_233 = x_256;
x_234 = x_257;
x_235 = x_258;
x_236 = x_259;
x_237 = x_294;
goto block_246;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_295 = lean_ctor_get(x_260, 0);
lean_inc(x_295);
lean_dec(x_260);
x_296 = l_Array_empty(lean_box(0));
x_297 = lean_array_push(x_296, x_295);
x_221 = x_247;
x_222 = x_248;
x_223 = x_249;
x_224 = x_251;
x_225 = x_250;
x_226 = x_252;
x_227 = x_254;
x_228 = x_253;
x_229 = x_285;
x_230 = x_287;
x_231 = x_289;
x_232 = x_292;
x_233 = x_256;
x_234 = x_257;
x_235 = x_258;
x_236 = x_259;
x_237 = x_297;
goto block_246;
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_298 = lean_ctor_get(x_287, 1);
lean_inc(x_298);
lean_dec(x_287);
x_299 = lean_mk_string_unchecked("tacticSimpa!_", 13, 13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_300 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_299);
x_301 = lean_mk_string_unchecked("simpa!", 6, 6);
lean_inc(x_285);
x_302 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_302, 0, x_285);
lean_ctor_set(x_302, 1, x_301);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_303; 
x_303 = l_Array_empty(lean_box(0));
x_221 = x_247;
x_222 = x_248;
x_223 = x_249;
x_224 = x_251;
x_225 = x_250;
x_226 = x_252;
x_227 = x_254;
x_228 = x_253;
x_229 = x_285;
x_230 = x_302;
x_231 = x_298;
x_232 = x_300;
x_233 = x_256;
x_234 = x_257;
x_235 = x_258;
x_236 = x_259;
x_237 = x_303;
goto block_246;
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_304 = lean_ctor_get(x_260, 0);
lean_inc(x_304);
lean_dec(x_260);
x_305 = l_Array_empty(lean_box(0));
x_306 = lean_array_push(x_305, x_304);
x_221 = x_247;
x_222 = x_248;
x_223 = x_249;
x_224 = x_251;
x_225 = x_250;
x_226 = x_252;
x_227 = x_254;
x_228 = x_253;
x_229 = x_285;
x_230 = x_302;
x_231 = x_298;
x_232 = x_300;
x_233 = x_256;
x_234 = x_257;
x_235 = x_258;
x_236 = x_259;
x_237 = x_306;
goto block_246;
}
}
}
else
{
uint8_t x_307; 
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_254);
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_34);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_307 = !lean_is_exclusive(x_284);
if (x_307 == 0)
{
return x_284;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_308 = lean_ctor_get(x_284, 0);
x_309 = lean_ctor_get(x_284, 1);
lean_inc(x_309);
lean_inc(x_308);
lean_dec(x_284);
x_310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_310, 0, x_308);
lean_ctor_set(x_310, 1, x_309);
return x_310;
}
}
}
}
block_349:
{
lean_object* x_327; lean_object* x_328; uint8_t x_329; 
x_327 = lean_unsigned_to_nat(5u);
x_328 = l_Lean_Syntax_getArg(x_313, x_327);
lean_dec(x_313);
x_329 = l_Lean_Syntax_matchesNull(x_328, x_13);
if (x_329 == 0)
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
lean_dec(x_317);
lean_dec(x_316);
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_312);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_330 = lean_mk_string_unchecked("Lean.Elab.Tactic.Simpa", 22, 22);
x_331 = lean_mk_string_unchecked("Lean.Elab.Tactic.Simpa.evalSimpa", 32, 32);
x_332 = lean_unsigned_to_nat(105u);
x_333 = lean_unsigned_to_nat(17u);
x_334 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_335 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_330, x_331, x_332, x_333, x_334);
lean_dec(x_334);
lean_dec(x_331);
lean_dec(x_330);
lean_inc(x_325);
lean_inc(x_324);
lean_inc(x_323);
lean_inc(x_322);
lean_inc(x_321);
lean_inc(x_320);
lean_inc(x_319);
lean_inc(x_318);
x_336 = l_panic___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__0(x_335, x_318, x_319, x_320, x_321, x_322, x_323, x_324, x_325, x_326);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_336, 1);
lean_inc(x_338);
lean_dec(x_336);
x_339 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2(x_1, x_34, x_337, x_318, x_319, x_320, x_321, x_322, x_323, x_324, x_325, x_338);
return x_339;
}
else
{
uint8_t x_340; 
lean_dec(x_325);
lean_dec(x_324);
lean_dec(x_323);
lean_dec(x_322);
lean_dec(x_321);
lean_dec(x_320);
lean_dec(x_319);
lean_dec(x_318);
lean_dec(x_34);
x_340 = !lean_is_exclusive(x_336);
if (x_340 == 0)
{
return x_336;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_341 = lean_ctor_get(x_336, 0);
x_342 = lean_ctor_get(x_336, 1);
lean_inc(x_342);
lean_inc(x_341);
lean_dec(x_336);
x_343 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_343, 0, x_341);
lean_ctor_set(x_343, 1, x_342);
return x_343;
}
}
}
else
{
lean_object* x_344; 
x_344 = l_Lean_Syntax_getOptional_x3f(x_316);
lean_dec(x_316);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_345; 
x_345 = lean_box(0);
x_247 = x_319;
x_248 = x_314;
x_249 = x_318;
x_250 = x_325;
x_251 = x_315;
x_252 = x_324;
x_253 = x_320;
x_254 = x_312;
x_255 = x_326;
x_256 = x_322;
x_257 = x_317;
x_258 = x_321;
x_259 = x_323;
x_260 = x_345;
goto block_311;
}
else
{
uint8_t x_346; 
x_346 = !lean_is_exclusive(x_344);
if (x_346 == 0)
{
x_247 = x_319;
x_248 = x_314;
x_249 = x_318;
x_250 = x_325;
x_251 = x_315;
x_252 = x_324;
x_253 = x_320;
x_254 = x_312;
x_255 = x_326;
x_256 = x_322;
x_257 = x_317;
x_258 = x_321;
x_259 = x_323;
x_260 = x_344;
goto block_311;
}
else
{
lean_object* x_347; lean_object* x_348; 
x_347 = lean_ctor_get(x_344, 0);
lean_inc(x_347);
lean_dec(x_344);
x_348 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_348, 0, x_347);
x_247 = x_319;
x_248 = x_314;
x_249 = x_318;
x_250 = x_325;
x_251 = x_315;
x_252 = x_324;
x_253 = x_320;
x_254 = x_312;
x_255 = x_326;
x_256 = x_322;
x_257 = x_317;
x_258 = x_321;
x_259 = x_323;
x_260 = x_348;
goto block_311;
}
}
}
}
block_377:
{
lean_object* x_356; uint8_t x_357; 
x_356 = l_Lean_Syntax_getArg(x_351, x_14);
x_357 = l_Lean_Syntax_isNone(x_356);
if (x_357 == 0)
{
uint8_t x_358; 
lean_inc(x_356);
x_358 = l_Lean_Syntax_matchesNull(x_356, x_15);
if (x_358 == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
lean_dec(x_356);
lean_dec(x_354);
lean_dec(x_353);
lean_dec(x_352);
lean_dec(x_351);
lean_dec(x_350);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_359 = lean_mk_string_unchecked("Lean.Elab.Tactic.Simpa", 22, 22);
x_360 = lean_mk_string_unchecked("Lean.Elab.Tactic.Simpa.evalSimpa", 32, 32);
x_361 = lean_unsigned_to_nat(105u);
x_362 = lean_unsigned_to_nat(17u);
x_363 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_364 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_359, x_360, x_361, x_362, x_363);
lean_dec(x_363);
lean_dec(x_360);
lean_dec(x_359);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
x_365 = l_panic___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__0(x_364, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_355);
if (lean_obj_tag(x_365) == 0)
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_365, 1);
lean_inc(x_367);
lean_dec(x_365);
x_368 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2(x_1, x_34, x_366, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_367);
return x_368;
}
else
{
uint8_t x_369; 
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
x_369 = !lean_is_exclusive(x_365);
if (x_369 == 0)
{
return x_365;
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_370 = lean_ctor_get(x_365, 0);
x_371 = lean_ctor_get(x_365, 1);
lean_inc(x_371);
lean_inc(x_370);
lean_dec(x_365);
x_372 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_372, 0, x_370);
lean_ctor_set(x_372, 1, x_371);
return x_372;
}
}
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_373 = l_Lean_Syntax_getArg(x_356, x_16);
lean_dec(x_356);
x_374 = l_Lean_Syntax_getArgs(x_373);
lean_dec(x_373);
x_375 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_375, 0, x_374);
x_312 = x_350;
x_313 = x_351;
x_314 = x_352;
x_315 = x_354;
x_316 = x_353;
x_317 = x_375;
x_318 = x_25;
x_319 = x_26;
x_320 = x_27;
x_321 = x_28;
x_322 = x_29;
x_323 = x_30;
x_324 = x_31;
x_325 = x_32;
x_326 = x_355;
goto block_349;
}
}
else
{
lean_object* x_376; 
lean_dec(x_356);
x_376 = lean_box(0);
x_312 = x_350;
x_313 = x_351;
x_314 = x_352;
x_315 = x_354;
x_316 = x_353;
x_317 = x_376;
x_318 = x_25;
x_319 = x_26;
x_320 = x_27;
x_321 = x_28;
x_322 = x_29;
x_323 = x_30;
x_324 = x_31;
x_325 = x_32;
x_326 = x_355;
goto block_349;
}
}
block_440:
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_379 = l_Lean_Syntax_unsetTrailing(x_17);
x_380 = lean_ctor_get(x_24, 0);
lean_inc(x_380);
lean_dec(x_24);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
x_381 = l_Lean_Elab_Tactic_mkSimpOnly(x_379, x_380, x_29, x_30, x_31, x_32, x_33);
lean_dec(x_380);
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_382; lean_object* x_383; uint8_t x_384; 
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_381, 1);
lean_inc(x_383);
lean_dec(x_381);
lean_inc(x_382);
x_384 = l_Lean_Syntax_isOfKind(x_382, x_18);
if (x_384 == 0)
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
lean_dec(x_382);
lean_dec(x_378);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_385 = lean_mk_string_unchecked("Lean.Elab.Tactic.Simpa", 22, 22);
x_386 = lean_mk_string_unchecked("Lean.Elab.Tactic.Simpa.evalSimpa", 32, 32);
x_387 = lean_unsigned_to_nat(105u);
x_388 = lean_unsigned_to_nat(17u);
x_389 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_390 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_385, x_386, x_387, x_388, x_389);
lean_dec(x_389);
lean_dec(x_386);
lean_dec(x_385);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
x_391 = l_panic___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__0(x_390, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_383);
if (lean_obj_tag(x_391) == 0)
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_392 = lean_ctor_get(x_391, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_391, 1);
lean_inc(x_393);
lean_dec(x_391);
x_394 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2(x_1, x_34, x_392, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_393);
return x_394;
}
else
{
uint8_t x_395; 
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
x_395 = !lean_is_exclusive(x_391);
if (x_395 == 0)
{
return x_391;
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_396 = lean_ctor_get(x_391, 0);
x_397 = lean_ctor_get(x_391, 1);
lean_inc(x_397);
lean_inc(x_396);
lean_dec(x_391);
x_398 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_398, 0, x_396);
lean_ctor_set(x_398, 1, x_397);
return x_398;
}
}
}
else
{
lean_object* x_399; uint8_t x_400; 
x_399 = l_Lean_Syntax_getArg(x_382, x_16);
lean_inc(x_399);
x_400 = l_Lean_Syntax_isOfKind(x_399, x_19);
if (x_400 == 0)
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
lean_dec(x_399);
lean_dec(x_382);
lean_dec(x_378);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_401 = lean_mk_string_unchecked("Lean.Elab.Tactic.Simpa", 22, 22);
x_402 = lean_mk_string_unchecked("Lean.Elab.Tactic.Simpa.evalSimpa", 32, 32);
x_403 = lean_unsigned_to_nat(105u);
x_404 = lean_unsigned_to_nat(17u);
x_405 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_406 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_401, x_402, x_403, x_404, x_405);
lean_dec(x_405);
lean_dec(x_402);
lean_dec(x_401);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
x_407 = l_panic___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__0(x_406, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_383);
if (lean_obj_tag(x_407) == 0)
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_407, 1);
lean_inc(x_409);
lean_dec(x_407);
x_410 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2(x_1, x_34, x_408, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_409);
return x_410;
}
else
{
uint8_t x_411; 
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
x_411 = !lean_is_exclusive(x_407);
if (x_411 == 0)
{
return x_407;
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; 
x_412 = lean_ctor_get(x_407, 0);
x_413 = lean_ctor_get(x_407, 1);
lean_inc(x_413);
lean_inc(x_412);
lean_dec(x_407);
x_414 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_414, 0, x_412);
lean_ctor_set(x_414, 1, x_413);
return x_414;
}
}
}
else
{
lean_object* x_415; lean_object* x_416; uint8_t x_417; 
x_415 = l_Lean_Syntax_getArg(x_382, x_20);
x_416 = l_Lean_Syntax_getArg(x_382, x_15);
x_417 = l_Lean_Syntax_isNone(x_416);
if (x_417 == 0)
{
uint8_t x_418; 
lean_inc(x_416);
x_418 = l_Lean_Syntax_matchesNull(x_416, x_16);
if (x_418 == 0)
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
lean_dec(x_416);
lean_dec(x_415);
lean_dec(x_399);
lean_dec(x_382);
lean_dec(x_378);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_419 = lean_mk_string_unchecked("Lean.Elab.Tactic.Simpa", 22, 22);
x_420 = lean_mk_string_unchecked("Lean.Elab.Tactic.Simpa.evalSimpa", 32, 32);
x_421 = lean_unsigned_to_nat(105u);
x_422 = lean_unsigned_to_nat(17u);
x_423 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_424 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_419, x_420, x_421, x_422, x_423);
lean_dec(x_423);
lean_dec(x_420);
lean_dec(x_419);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
x_425 = l_panic___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__0(x_424, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_383);
if (lean_obj_tag(x_425) == 0)
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_426 = lean_ctor_get(x_425, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_425, 1);
lean_inc(x_427);
lean_dec(x_425);
x_428 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2(x_1, x_34, x_426, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_427);
return x_428;
}
else
{
uint8_t x_429; 
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
x_429 = !lean_is_exclusive(x_425);
if (x_429 == 0)
{
return x_425;
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; 
x_430 = lean_ctor_get(x_425, 0);
x_431 = lean_ctor_get(x_425, 1);
lean_inc(x_431);
lean_inc(x_430);
lean_dec(x_425);
x_432 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_432, 0, x_430);
lean_ctor_set(x_432, 1, x_431);
return x_432;
}
}
}
else
{
lean_object* x_433; lean_object* x_434; 
x_433 = l_Lean_Syntax_getArg(x_416, x_13);
lean_dec(x_416);
x_434 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_434, 0, x_433);
x_350 = x_378;
x_351 = x_382;
x_352 = x_399;
x_353 = x_415;
x_354 = x_434;
x_355 = x_383;
goto block_377;
}
}
else
{
lean_object* x_435; 
lean_dec(x_416);
x_435 = lean_box(0);
x_350 = x_378;
x_351 = x_382;
x_352 = x_399;
x_353 = x_415;
x_354 = x_435;
x_355 = x_383;
goto block_377;
}
}
}
}
else
{
uint8_t x_436; 
lean_dec(x_378);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_436 = !lean_is_exclusive(x_381);
if (x_436 == 0)
{
return x_381;
}
else
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_437 = lean_ctor_get(x_381, 0);
x_438 = lean_ctor_get(x_381, 1);
lean_inc(x_438);
lean_inc(x_437);
lean_dec(x_381);
x_439 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_439, 0, x_437);
lean_ctor_set(x_439, 1, x_438);
return x_439;
}
}
}
block_447:
{
if (lean_obj_tag(x_21) == 0)
{
x_378 = x_21;
goto block_440;
}
else
{
uint8_t x_441; 
x_441 = !lean_is_exclusive(x_21);
if (x_441 == 0)
{
lean_object* x_442; lean_object* x_443; 
x_442 = lean_ctor_get(x_21, 0);
x_443 = l_Lean_Syntax_unsetTrailing(x_442);
lean_ctor_set(x_21, 0, x_443);
x_378 = x_21;
goto block_440;
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_444 = lean_ctor_get(x_21, 0);
lean_inc(x_444);
lean_dec(x_21);
x_445 = l_Lean_Syntax_unsetTrailing(x_444);
x_446 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_446, 0, x_445);
x_378 = x_446;
goto block_440;
}
}
}
block_451:
{
if (x_448 == 0)
{
lean_object* x_449; lean_object* x_450; 
lean_dec(x_34);
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_449 = lean_box(0);
x_450 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__1(x_24, x_449, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
return x_450;
}
else
{
goto block_447;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; 
x_19 = l_Lean_MVarId_getType(x_1, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_mk_syntax_ident(x_2);
lean_inc(x_20);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_20);
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_24 = l_Lean_Elab_Term_elabTerm(x_22, x_23, x_3, x_3, x_12, x_13, x_14, x_15, x_16, x_17, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_27 = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(x_4, x_12, x_13, x_14, x_15, x_16, x_17, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_29 = x_27;
} else {
 lean_dec_ref(x_27);
 x_29 = lean_box(0);
}
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_25);
x_30 = lean_infer_type(x_25, x_14, x_15, x_16, x_17, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; lean_object* x_74; uint64_t x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_56 = lean_ctor_get(x_14, 0);
lean_inc(x_56);
x_57 = lean_ctor_get_uint8(x_56, 0);
x_58 = lean_ctor_get_uint8(x_56, 1);
x_59 = lean_ctor_get_uint8(x_56, 2);
x_60 = lean_ctor_get_uint8(x_56, 3);
x_61 = lean_ctor_get_uint8(x_56, 4);
x_62 = lean_ctor_get_uint8(x_56, 5);
x_63 = lean_ctor_get_uint8(x_56, 6);
x_64 = lean_ctor_get_uint8(x_56, 8);
x_65 = lean_ctor_get_uint8(x_56, 9);
x_66 = lean_ctor_get_uint8(x_56, 10);
x_67 = lean_ctor_get_uint8(x_56, 11);
x_68 = lean_ctor_get_uint8(x_56, 12);
x_69 = lean_ctor_get_uint8(x_56, 13);
x_70 = lean_ctor_get_uint8(x_56, 14);
x_71 = lean_ctor_get_uint8(x_56, 15);
x_72 = lean_ctor_get_uint8(x_56, 16);
x_73 = lean_ctor_get_uint8(x_56, 17);
lean_dec(x_56);
x_74 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_74, 0, x_57);
lean_ctor_set_uint8(x_74, 1, x_58);
lean_ctor_set_uint8(x_74, 2, x_59);
lean_ctor_set_uint8(x_74, 3, x_60);
lean_ctor_set_uint8(x_74, 4, x_61);
lean_ctor_set_uint8(x_74, 5, x_62);
lean_ctor_set_uint8(x_74, 6, x_63);
lean_ctor_set_uint8(x_74, 7, x_9);
lean_ctor_set_uint8(x_74, 8, x_64);
lean_ctor_set_uint8(x_74, 9, x_65);
lean_ctor_set_uint8(x_74, 10, x_66);
lean_ctor_set_uint8(x_74, 11, x_67);
lean_ctor_set_uint8(x_74, 12, x_68);
lean_ctor_set_uint8(x_74, 13, x_69);
lean_ctor_set_uint8(x_74, 14, x_70);
lean_ctor_set_uint8(x_74, 15, x_71);
lean_ctor_set_uint8(x_74, 16, x_72);
lean_ctor_set_uint8(x_74, 17, x_73);
x_75 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_74);
x_76 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 8);
x_77 = lean_ctor_get(x_14, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_14, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_14, 3);
lean_inc(x_79);
x_80 = lean_ctor_get(x_14, 4);
lean_inc(x_80);
x_81 = lean_ctor_get(x_14, 5);
lean_inc(x_81);
x_82 = lean_ctor_get(x_14, 6);
lean_inc(x_82);
x_83 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 9);
x_84 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 10);
x_85 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_85, 0, x_74);
lean_ctor_set(x_85, 1, x_77);
lean_ctor_set(x_85, 2, x_78);
lean_ctor_set(x_85, 3, x_79);
lean_ctor_set(x_85, 4, x_80);
lean_ctor_set(x_85, 5, x_81);
lean_ctor_set(x_85, 6, x_82);
lean_ctor_set_uint64(x_85, sizeof(void*)*7, x_75);
lean_ctor_set_uint8(x_85, sizeof(void*)*7 + 8, x_76);
lean_ctor_set_uint8(x_85, sizeof(void*)*7 + 9, x_83);
lean_ctor_set_uint8(x_85, sizeof(void*)*7 + 10, x_84);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_31);
lean_inc(x_20);
x_86 = l_Lean_Meta_isExprDefEq(x_20, x_31, x_85, x_15, x_16, x_17, x_32);
lean_dec(x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_unbox(x_87);
lean_dec(x_87);
x_33 = x_89;
x_34 = x_88;
goto block_55;
}
else
{
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_90 = lean_ctor_get(x_86, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_86, 1);
lean_inc(x_91);
lean_dec(x_86);
x_92 = lean_unbox(x_90);
lean_dec(x_90);
x_33 = x_92;
x_34 = x_91;
goto block_55;
}
else
{
uint8_t x_93; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_93 = !lean_is_exclusive(x_86);
if (x_93 == 0)
{
return x_86;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_86, 0);
x_95 = lean_ctor_get(x_86, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_86);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
block_55:
{
if (x_33 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
x_35 = lean_mk_string_unchecked("type mismatch, term", 19, 19);
x_36 = l_Lean_stringToMessageData(x_35);
lean_dec(x_35);
x_37 = l_Lean_indentExpr(x_5);
if (lean_is_scalar(x_29)) {
 x_38 = lean_alloc_ctor(7, 2, 0);
} else {
 x_38 = x_29;
 lean_ctor_set_tag(x_38, 7);
}
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_mk_string_unchecked("\nafter simplification", 21, 21);
x_40 = l_Lean_stringToMessageData(x_39);
lean_dec(x_39);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_box(0);
x_44 = l_Lean_Elab_Term_throwTypeMismatchError(lean_box(0), x_42, x_20, x_31, x_25, x_8, x_43, x_14, x_15, x_16, x_17, x_34);
lean_dec(x_42);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_20);
lean_dec(x_8);
x_45 = l_Lean_Meta_getMVars(x_5, x_14, x_15, x_16, x_17, x_34);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Elab_Tactic_filterOldMVars___redArg(x_46, x_6, x_15, x_47);
lean_dec(x_46);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
x_51 = l_Lean_Elab_Tactic_logUnassignedAndAbort(x_49, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_50);
lean_dec(x_49);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = l_Lean_Name_mkStr1(x_7);
x_54 = l_Lean_Elab_Tactic_closeMainGoal___redArg(x_53, x_25, x_4, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_52);
return x_54;
}
else
{
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
return x_51;
}
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_97 = !lean_is_exclusive(x_30);
if (x_97 == 0)
{
return x_30;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_30, 0);
x_99 = lean_ctor_get(x_30, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_30);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_27;
}
}
else
{
uint8_t x_101; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_101 = !lean_is_exclusive(x_24);
if (x_101 == 0)
{
return x_24;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_24, 0);
x_103 = lean_ctor_get(x_24, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_24);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_105 = !lean_is_exclusive(x_19);
if (x_105 == 0)
{
return x_19;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_19, 0);
x_107 = lean_ctor_get(x_19, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_19);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Lean_MVarId_assign___at___Lean_Elab_Tactic_refineCore_spec__0(x_1, x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_apply_10(x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, uint8_t x_10, lean_object* x_11, uint8_t x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22) {
_start:
{
lean_object* x_23; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_11);
x_60 = lean_ctor_get(x_18, 2);
lean_inc(x_60);
x_61 = lean_mk_string_unchecked("this", 4, 4);
x_62 = l_Lean_Name_mkStr1(x_61);
x_63 = l_Lean_LocalContext_findFromUserName_x3f(x_60, x_62);
lean_dec(x_62);
lean_dec(x_60);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_64 = l_Lean_MVarId_assumption(x_2, x_18, x_19, x_20, x_21, x_22);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_apply_10(x_3, x_4, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_65);
return x_66;
}
else
{
uint8_t x_67; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
x_67 = !lean_is_exclusive(x_64);
if (x_67 == 0)
{
return x_64;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_64, 0);
x_69 = lean_ctor_get(x_64, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_64);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_63, 0);
lean_inc(x_71);
lean_dec(x_63);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_23 = x_72;
goto block_46;
}
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_73 = lean_ctor_get(x_1, 0);
lean_inc(x_73);
lean_dec(x_1);
x_74 = lean_st_ref_get(x_19, x_22);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_74, 0);
x_77 = lean_ctor_get(x_74, 1);
x_78 = lean_box(0);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_79 = l_Lean_Elab_Tactic_elabTerm(x_73, x_78, x_10, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_77);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
lean_inc(x_80);
x_82 = l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3(x_2, x_80, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_81);
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_153; 
x_84 = lean_ctor_get(x_82, 0);
x_85 = lean_ctor_get(x_82, 1);
x_86 = lean_ctor_get(x_76, 0);
lean_inc(x_86);
lean_dec(x_76);
x_87 = lean_ctor_get(x_86, 2);
lean_inc(x_87);
lean_dec(x_86);
x_153 = lean_unbox(x_84);
lean_dec(x_84);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
lean_dec(x_87);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_154 = lean_mk_string_unchecked("occurs check failed, expression", 31, 31);
x_155 = l_Lean_stringToMessageData(x_154);
lean_dec(x_154);
x_156 = l_Lean_indentExpr(x_80);
lean_ctor_set_tag(x_82, 7);
lean_ctor_set(x_82, 1, x_156);
lean_ctor_set(x_82, 0, x_155);
x_157 = lean_mk_string_unchecked("\ncontains the goal ", 19, 19);
x_158 = l_Lean_stringToMessageData(x_157);
lean_dec(x_157);
lean_ctor_set_tag(x_74, 7);
lean_ctor_set(x_74, 1, x_158);
lean_ctor_set(x_74, 0, x_82);
x_159 = l_Lean_Expr_mvar___override(x_2);
x_160 = l_Lean_MessageData_ofExpr(x_159);
x_161 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_161, 0, x_74);
lean_ctor_set(x_161, 1, x_160);
x_162 = lean_mk_string_unchecked("", 0, 0);
x_163 = l_Lean_stringToMessageData(x_162);
lean_dec(x_162);
x_164 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_163);
x_165 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_164, x_18, x_19, x_20, x_21, x_85);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_166 = !lean_is_exclusive(x_165);
if (x_166 == 0)
{
return x_165;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_165, 0);
x_168 = lean_ctor_get(x_165, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_165);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
else
{
lean_object* x_170; 
lean_free_object(x_74);
lean_inc(x_2);
x_170 = l_Lean_MVarId_getType(x_2, x_18, x_19, x_20, x_21, x_85);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
lean_inc(x_2);
x_173 = l_Lean_MVarId_getTag(x_2, x_18, x_19, x_20, x_21, x_172);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
lean_inc(x_18);
x_176 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_171, x_174, x_18, x_19, x_20, x_21, x_175);
x_177 = !lean_is_exclusive(x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_178 = lean_ctor_get(x_176, 0);
x_179 = lean_ctor_get(x_176, 1);
x_180 = l_Lean_Expr_mvarId_x21(x_178);
x_181 = lean_mk_string_unchecked("h", 1, 1);
x_182 = l_Lean_Name_mkStr1(x_181);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_80);
lean_inc(x_182);
x_183 = l_Lean_MVarId_note(x_180, x_182, x_80, x_78, x_18, x_19, x_20, x_21, x_179);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
x_186 = !lean_is_exclusive(x_184);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_187 = lean_ctor_get(x_184, 0);
x_188 = lean_ctor_get(x_184, 1);
x_189 = lean_mk_empty_array_with_capacity(x_5);
lean_inc(x_187);
x_190 = lean_array_push(x_189, x_187);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_191 = l_Lean_Meta_simpGoal(x_188, x_6, x_7, x_8, x_9, x_190, x_4, x_18, x_19, x_20, x_21, x_185);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
x_194 = !lean_is_exclusive(x_192);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_192, 0);
x_196 = lean_ctor_get(x_192, 1);
lean_inc(x_196);
lean_inc(x_3);
lean_inc(x_178);
lean_inc(x_2);
x_197 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___boxed), 14, 4);
lean_closure_set(x_197, 0, x_2);
lean_closure_set(x_197, 1, x_178);
lean_closure_set(x_197, 2, x_3);
lean_closure_set(x_197, 3, x_196);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_198; uint8_t x_199; 
lean_dec(x_187);
lean_dec(x_182);
lean_dec(x_87);
lean_dec(x_11);
x_198 = lean_ctor_get(x_20, 2);
lean_inc(x_198);
x_199 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(x_198);
lean_dec(x_198);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; 
lean_dec(x_197);
lean_free_object(x_192);
lean_free_object(x_184);
lean_free_object(x_176);
lean_free_object(x_82);
lean_dec(x_80);
x_200 = lean_box(0);
x_201 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5(x_2, x_178, x_3, x_196, x_200, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_193);
return x_201;
}
else
{
if (lean_obj_tag(x_80) == 1)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_80, 0);
lean_inc(x_202);
lean_dec(x_80);
x_203 = lean_ctor_get(x_18, 2);
lean_inc(x_203);
lean_inc(x_202);
x_204 = l_Lean_LocalContext_getRoundtrippingUserName_x3f(x_203, x_202);
if (lean_obj_tag(x_204) == 0)
{
lean_dec(x_202);
lean_free_object(x_192);
lean_dec(x_196);
lean_free_object(x_184);
lean_free_object(x_176);
lean_dec(x_178);
lean_free_object(x_82);
lean_dec(x_3);
lean_dec(x_2);
x_47 = x_21;
x_48 = x_19;
x_49 = x_15;
x_50 = x_193;
x_51 = x_197;
x_52 = x_18;
x_53 = x_16;
x_54 = x_20;
x_55 = x_17;
x_56 = x_14;
goto block_59;
}
else
{
lean_dec(x_204);
if (x_12 == 0)
{
lean_dec(x_202);
lean_free_object(x_192);
lean_dec(x_196);
lean_free_object(x_184);
lean_free_object(x_176);
lean_dec(x_178);
lean_free_object(x_82);
lean_dec(x_3);
lean_dec(x_2);
x_47 = x_21;
x_48 = x_19;
x_49 = x_15;
x_50 = x_193;
x_51 = x_197;
x_52 = x_18;
x_53 = x_16;
x_54 = x_20;
x_55 = x_17;
x_56 = x_14;
goto block_59;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_197);
x_205 = lean_ctor_get(x_20, 5);
lean_inc(x_205);
x_206 = l_linter_unnecessarySimpa;
x_207 = lean_mk_string_unchecked("try 'simp at ", 13, 13);
x_208 = l_Lean_stringToMessageData(x_207);
lean_dec(x_207);
x_209 = l_Lean_Expr_fvar___override(x_202);
x_210 = l_Lean_MessageData_ofExpr(x_209);
lean_inc(x_210);
lean_ctor_set_tag(x_192, 7);
lean_ctor_set(x_192, 1, x_210);
lean_ctor_set(x_192, 0, x_208);
x_211 = lean_mk_string_unchecked("' instead of 'simpa using ", 26, 26);
x_212 = l_Lean_stringToMessageData(x_211);
lean_dec(x_211);
lean_ctor_set_tag(x_184, 7);
lean_ctor_set(x_184, 1, x_212);
lean_ctor_set(x_184, 0, x_192);
lean_ctor_set_tag(x_176, 7);
lean_ctor_set(x_176, 1, x_210);
lean_ctor_set(x_176, 0, x_184);
x_213 = lean_mk_string_unchecked("'", 1, 1);
x_214 = l_Lean_stringToMessageData(x_213);
lean_dec(x_213);
lean_ctor_set_tag(x_82, 7);
lean_ctor_set(x_82, 1, x_214);
lean_ctor_set(x_82, 0, x_176);
lean_inc(x_20);
x_215 = l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1(x_206, x_205, x_82, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_193);
lean_dec(x_205);
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec(x_215);
x_218 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5(x_2, x_178, x_3, x_196, x_216, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_217);
lean_dec(x_216);
return x_218;
}
}
}
else
{
lean_object* x_219; lean_object* x_220; 
lean_dec(x_197);
lean_free_object(x_192);
lean_free_object(x_184);
lean_free_object(x_176);
lean_free_object(x_82);
lean_dec(x_80);
x_219 = lean_box(0);
x_220 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5(x_2, x_178, x_3, x_196, x_219, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_193);
return x_220;
}
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
lean_free_object(x_192);
lean_dec(x_196);
lean_free_object(x_184);
lean_free_object(x_176);
lean_dec(x_178);
lean_free_object(x_82);
lean_dec(x_3);
lean_dec(x_2);
x_221 = lean_ctor_get(x_195, 0);
lean_inc(x_221);
lean_dec(x_195);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
x_224 = lean_array_get_size(x_222);
x_225 = lean_nat_dec_lt(x_13, x_224);
lean_dec(x_224);
if (x_225 == 0)
{
lean_dec(x_222);
x_88 = x_21;
x_89 = x_223;
x_90 = x_15;
x_91 = x_19;
x_92 = x_197;
x_93 = x_193;
x_94 = x_18;
x_95 = x_16;
x_96 = x_17;
x_97 = x_14;
x_98 = x_20;
x_99 = x_182;
x_100 = x_187;
goto block_152;
}
else
{
lean_object* x_226; 
lean_dec(x_187);
x_226 = lean_array_fget(x_222, x_13);
lean_dec(x_222);
x_88 = x_21;
x_89 = x_223;
x_90 = x_15;
x_91 = x_19;
x_92 = x_197;
x_93 = x_193;
x_94 = x_18;
x_95 = x_16;
x_96 = x_17;
x_97 = x_14;
x_98 = x_20;
x_99 = x_182;
x_100 = x_226;
goto block_152;
}
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_192, 0);
x_228 = lean_ctor_get(x_192, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_192);
lean_inc(x_228);
lean_inc(x_3);
lean_inc(x_178);
lean_inc(x_2);
x_229 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___boxed), 14, 4);
lean_closure_set(x_229, 0, x_2);
lean_closure_set(x_229, 1, x_178);
lean_closure_set(x_229, 2, x_3);
lean_closure_set(x_229, 3, x_228);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_230; uint8_t x_231; 
lean_dec(x_187);
lean_dec(x_182);
lean_dec(x_87);
lean_dec(x_11);
x_230 = lean_ctor_get(x_20, 2);
lean_inc(x_230);
x_231 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(x_230);
lean_dec(x_230);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; 
lean_dec(x_229);
lean_free_object(x_184);
lean_free_object(x_176);
lean_free_object(x_82);
lean_dec(x_80);
x_232 = lean_box(0);
x_233 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5(x_2, x_178, x_3, x_228, x_232, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_193);
return x_233;
}
else
{
if (lean_obj_tag(x_80) == 1)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_80, 0);
lean_inc(x_234);
lean_dec(x_80);
x_235 = lean_ctor_get(x_18, 2);
lean_inc(x_235);
lean_inc(x_234);
x_236 = l_Lean_LocalContext_getRoundtrippingUserName_x3f(x_235, x_234);
if (lean_obj_tag(x_236) == 0)
{
lean_dec(x_234);
lean_dec(x_228);
lean_free_object(x_184);
lean_free_object(x_176);
lean_dec(x_178);
lean_free_object(x_82);
lean_dec(x_3);
lean_dec(x_2);
x_47 = x_21;
x_48 = x_19;
x_49 = x_15;
x_50 = x_193;
x_51 = x_229;
x_52 = x_18;
x_53 = x_16;
x_54 = x_20;
x_55 = x_17;
x_56 = x_14;
goto block_59;
}
else
{
lean_dec(x_236);
if (x_12 == 0)
{
lean_dec(x_234);
lean_dec(x_228);
lean_free_object(x_184);
lean_free_object(x_176);
lean_dec(x_178);
lean_free_object(x_82);
lean_dec(x_3);
lean_dec(x_2);
x_47 = x_21;
x_48 = x_19;
x_49 = x_15;
x_50 = x_193;
x_51 = x_229;
x_52 = x_18;
x_53 = x_16;
x_54 = x_20;
x_55 = x_17;
x_56 = x_14;
goto block_59;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_229);
x_237 = lean_ctor_get(x_20, 5);
lean_inc(x_237);
x_238 = l_linter_unnecessarySimpa;
x_239 = lean_mk_string_unchecked("try 'simp at ", 13, 13);
x_240 = l_Lean_stringToMessageData(x_239);
lean_dec(x_239);
x_241 = l_Lean_Expr_fvar___override(x_234);
x_242 = l_Lean_MessageData_ofExpr(x_241);
lean_inc(x_242);
x_243 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_243, 0, x_240);
lean_ctor_set(x_243, 1, x_242);
x_244 = lean_mk_string_unchecked("' instead of 'simpa using ", 26, 26);
x_245 = l_Lean_stringToMessageData(x_244);
lean_dec(x_244);
lean_ctor_set_tag(x_184, 7);
lean_ctor_set(x_184, 1, x_245);
lean_ctor_set(x_184, 0, x_243);
lean_ctor_set_tag(x_176, 7);
lean_ctor_set(x_176, 1, x_242);
lean_ctor_set(x_176, 0, x_184);
x_246 = lean_mk_string_unchecked("'", 1, 1);
x_247 = l_Lean_stringToMessageData(x_246);
lean_dec(x_246);
lean_ctor_set_tag(x_82, 7);
lean_ctor_set(x_82, 1, x_247);
lean_ctor_set(x_82, 0, x_176);
lean_inc(x_20);
x_248 = l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1(x_238, x_237, x_82, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_193);
lean_dec(x_237);
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec(x_248);
x_251 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5(x_2, x_178, x_3, x_228, x_249, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_250);
lean_dec(x_249);
return x_251;
}
}
}
else
{
lean_object* x_252; lean_object* x_253; 
lean_dec(x_229);
lean_free_object(x_184);
lean_free_object(x_176);
lean_free_object(x_82);
lean_dec(x_80);
x_252 = lean_box(0);
x_253 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5(x_2, x_178, x_3, x_228, x_252, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_193);
return x_253;
}
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; 
lean_dec(x_228);
lean_free_object(x_184);
lean_free_object(x_176);
lean_dec(x_178);
lean_free_object(x_82);
lean_dec(x_3);
lean_dec(x_2);
x_254 = lean_ctor_get(x_227, 0);
lean_inc(x_254);
lean_dec(x_227);
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_254, 1);
lean_inc(x_256);
lean_dec(x_254);
x_257 = lean_array_get_size(x_255);
x_258 = lean_nat_dec_lt(x_13, x_257);
lean_dec(x_257);
if (x_258 == 0)
{
lean_dec(x_255);
x_88 = x_21;
x_89 = x_256;
x_90 = x_15;
x_91 = x_19;
x_92 = x_229;
x_93 = x_193;
x_94 = x_18;
x_95 = x_16;
x_96 = x_17;
x_97 = x_14;
x_98 = x_20;
x_99 = x_182;
x_100 = x_187;
goto block_152;
}
else
{
lean_object* x_259; 
lean_dec(x_187);
x_259 = lean_array_fget(x_255, x_13);
lean_dec(x_255);
x_88 = x_21;
x_89 = x_256;
x_90 = x_15;
x_91 = x_19;
x_92 = x_229;
x_93 = x_193;
x_94 = x_18;
x_95 = x_16;
x_96 = x_17;
x_97 = x_14;
x_98 = x_20;
x_99 = x_182;
x_100 = x_259;
goto block_152;
}
}
}
}
else
{
uint8_t x_260; 
lean_free_object(x_184);
lean_dec(x_187);
lean_dec(x_182);
lean_free_object(x_176);
lean_dec(x_178);
lean_dec(x_87);
lean_free_object(x_82);
lean_dec(x_80);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_260 = !lean_is_exclusive(x_191);
if (x_260 == 0)
{
return x_191;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_261 = lean_ctor_get(x_191, 0);
x_262 = lean_ctor_get(x_191, 1);
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_191);
x_263 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_263, 0, x_261);
lean_ctor_set(x_263, 1, x_262);
return x_263;
}
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_264 = lean_ctor_get(x_184, 0);
x_265 = lean_ctor_get(x_184, 1);
lean_inc(x_265);
lean_inc(x_264);
lean_dec(x_184);
x_266 = lean_mk_empty_array_with_capacity(x_5);
lean_inc(x_264);
x_267 = lean_array_push(x_266, x_264);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_268 = l_Lean_Meta_simpGoal(x_265, x_6, x_7, x_8, x_9, x_267, x_4, x_18, x_19, x_20, x_21, x_185);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
lean_dec(x_268);
x_271 = lean_ctor_get(x_269, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_269, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_273 = x_269;
} else {
 lean_dec_ref(x_269);
 x_273 = lean_box(0);
}
lean_inc(x_272);
lean_inc(x_3);
lean_inc(x_178);
lean_inc(x_2);
x_274 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___boxed), 14, 4);
lean_closure_set(x_274, 0, x_2);
lean_closure_set(x_274, 1, x_178);
lean_closure_set(x_274, 2, x_3);
lean_closure_set(x_274, 3, x_272);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_275; uint8_t x_276; 
lean_dec(x_264);
lean_dec(x_182);
lean_dec(x_87);
lean_dec(x_11);
x_275 = lean_ctor_get(x_20, 2);
lean_inc(x_275);
x_276 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(x_275);
lean_dec(x_275);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; 
lean_dec(x_274);
lean_dec(x_273);
lean_free_object(x_176);
lean_free_object(x_82);
lean_dec(x_80);
x_277 = lean_box(0);
x_278 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5(x_2, x_178, x_3, x_272, x_277, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_270);
return x_278;
}
else
{
if (lean_obj_tag(x_80) == 1)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_279 = lean_ctor_get(x_80, 0);
lean_inc(x_279);
lean_dec(x_80);
x_280 = lean_ctor_get(x_18, 2);
lean_inc(x_280);
lean_inc(x_279);
x_281 = l_Lean_LocalContext_getRoundtrippingUserName_x3f(x_280, x_279);
if (lean_obj_tag(x_281) == 0)
{
lean_dec(x_279);
lean_dec(x_273);
lean_dec(x_272);
lean_free_object(x_176);
lean_dec(x_178);
lean_free_object(x_82);
lean_dec(x_3);
lean_dec(x_2);
x_47 = x_21;
x_48 = x_19;
x_49 = x_15;
x_50 = x_270;
x_51 = x_274;
x_52 = x_18;
x_53 = x_16;
x_54 = x_20;
x_55 = x_17;
x_56 = x_14;
goto block_59;
}
else
{
lean_dec(x_281);
if (x_12 == 0)
{
lean_dec(x_279);
lean_dec(x_273);
lean_dec(x_272);
lean_free_object(x_176);
lean_dec(x_178);
lean_free_object(x_82);
lean_dec(x_3);
lean_dec(x_2);
x_47 = x_21;
x_48 = x_19;
x_49 = x_15;
x_50 = x_270;
x_51 = x_274;
x_52 = x_18;
x_53 = x_16;
x_54 = x_20;
x_55 = x_17;
x_56 = x_14;
goto block_59;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_dec(x_274);
x_282 = lean_ctor_get(x_20, 5);
lean_inc(x_282);
x_283 = l_linter_unnecessarySimpa;
x_284 = lean_mk_string_unchecked("try 'simp at ", 13, 13);
x_285 = l_Lean_stringToMessageData(x_284);
lean_dec(x_284);
x_286 = l_Lean_Expr_fvar___override(x_279);
x_287 = l_Lean_MessageData_ofExpr(x_286);
lean_inc(x_287);
if (lean_is_scalar(x_273)) {
 x_288 = lean_alloc_ctor(7, 2, 0);
} else {
 x_288 = x_273;
 lean_ctor_set_tag(x_288, 7);
}
lean_ctor_set(x_288, 0, x_285);
lean_ctor_set(x_288, 1, x_287);
x_289 = lean_mk_string_unchecked("' instead of 'simpa using ", 26, 26);
x_290 = l_Lean_stringToMessageData(x_289);
lean_dec(x_289);
x_291 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_291, 0, x_288);
lean_ctor_set(x_291, 1, x_290);
lean_ctor_set_tag(x_176, 7);
lean_ctor_set(x_176, 1, x_287);
lean_ctor_set(x_176, 0, x_291);
x_292 = lean_mk_string_unchecked("'", 1, 1);
x_293 = l_Lean_stringToMessageData(x_292);
lean_dec(x_292);
lean_ctor_set_tag(x_82, 7);
lean_ctor_set(x_82, 1, x_293);
lean_ctor_set(x_82, 0, x_176);
lean_inc(x_20);
x_294 = l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1(x_283, x_282, x_82, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_270);
lean_dec(x_282);
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_294, 1);
lean_inc(x_296);
lean_dec(x_294);
x_297 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5(x_2, x_178, x_3, x_272, x_295, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_296);
lean_dec(x_295);
return x_297;
}
}
}
else
{
lean_object* x_298; lean_object* x_299; 
lean_dec(x_274);
lean_dec(x_273);
lean_free_object(x_176);
lean_free_object(x_82);
lean_dec(x_80);
x_298 = lean_box(0);
x_299 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5(x_2, x_178, x_3, x_272, x_298, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_270);
return x_299;
}
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_304; 
lean_dec(x_273);
lean_dec(x_272);
lean_free_object(x_176);
lean_dec(x_178);
lean_free_object(x_82);
lean_dec(x_3);
lean_dec(x_2);
x_300 = lean_ctor_get(x_271, 0);
lean_inc(x_300);
lean_dec(x_271);
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_300, 1);
lean_inc(x_302);
lean_dec(x_300);
x_303 = lean_array_get_size(x_301);
x_304 = lean_nat_dec_lt(x_13, x_303);
lean_dec(x_303);
if (x_304 == 0)
{
lean_dec(x_301);
x_88 = x_21;
x_89 = x_302;
x_90 = x_15;
x_91 = x_19;
x_92 = x_274;
x_93 = x_270;
x_94 = x_18;
x_95 = x_16;
x_96 = x_17;
x_97 = x_14;
x_98 = x_20;
x_99 = x_182;
x_100 = x_264;
goto block_152;
}
else
{
lean_object* x_305; 
lean_dec(x_264);
x_305 = lean_array_fget(x_301, x_13);
lean_dec(x_301);
x_88 = x_21;
x_89 = x_302;
x_90 = x_15;
x_91 = x_19;
x_92 = x_274;
x_93 = x_270;
x_94 = x_18;
x_95 = x_16;
x_96 = x_17;
x_97 = x_14;
x_98 = x_20;
x_99 = x_182;
x_100 = x_305;
goto block_152;
}
}
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
lean_dec(x_264);
lean_dec(x_182);
lean_free_object(x_176);
lean_dec(x_178);
lean_dec(x_87);
lean_free_object(x_82);
lean_dec(x_80);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_306 = lean_ctor_get(x_268, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_268, 1);
lean_inc(x_307);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 x_308 = x_268;
} else {
 lean_dec_ref(x_268);
 x_308 = lean_box(0);
}
if (lean_is_scalar(x_308)) {
 x_309 = lean_alloc_ctor(1, 2, 0);
} else {
 x_309 = x_308;
}
lean_ctor_set(x_309, 0, x_306);
lean_ctor_set(x_309, 1, x_307);
return x_309;
}
}
}
else
{
uint8_t x_310; 
lean_dec(x_182);
lean_free_object(x_176);
lean_dec(x_178);
lean_dec(x_87);
lean_free_object(x_82);
lean_dec(x_80);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_310 = !lean_is_exclusive(x_183);
if (x_310 == 0)
{
return x_183;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_311 = lean_ctor_get(x_183, 0);
x_312 = lean_ctor_get(x_183, 1);
lean_inc(x_312);
lean_inc(x_311);
lean_dec(x_183);
x_313 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_313, 0, x_311);
lean_ctor_set(x_313, 1, x_312);
return x_313;
}
}
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_314 = lean_ctor_get(x_176, 0);
x_315 = lean_ctor_get(x_176, 1);
lean_inc(x_315);
lean_inc(x_314);
lean_dec(x_176);
x_316 = l_Lean_Expr_mvarId_x21(x_314);
x_317 = lean_mk_string_unchecked("h", 1, 1);
x_318 = l_Lean_Name_mkStr1(x_317);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_80);
lean_inc(x_318);
x_319 = l_Lean_MVarId_note(x_316, x_318, x_80, x_78, x_18, x_19, x_20, x_21, x_315);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_319, 1);
lean_inc(x_321);
lean_dec(x_319);
x_322 = lean_ctor_get(x_320, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_320, 1);
lean_inc(x_323);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 lean_ctor_release(x_320, 1);
 x_324 = x_320;
} else {
 lean_dec_ref(x_320);
 x_324 = lean_box(0);
}
x_325 = lean_mk_empty_array_with_capacity(x_5);
lean_inc(x_322);
x_326 = lean_array_push(x_325, x_322);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_327 = l_Lean_Meta_simpGoal(x_323, x_6, x_7, x_8, x_9, x_326, x_4, x_18, x_19, x_20, x_21, x_321);
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_327, 1);
lean_inc(x_329);
lean_dec(x_327);
x_330 = lean_ctor_get(x_328, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_328, 1);
lean_inc(x_331);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 lean_ctor_release(x_328, 1);
 x_332 = x_328;
} else {
 lean_dec_ref(x_328);
 x_332 = lean_box(0);
}
lean_inc(x_331);
lean_inc(x_3);
lean_inc(x_314);
lean_inc(x_2);
x_333 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___boxed), 14, 4);
lean_closure_set(x_333, 0, x_2);
lean_closure_set(x_333, 1, x_314);
lean_closure_set(x_333, 2, x_3);
lean_closure_set(x_333, 3, x_331);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_334; uint8_t x_335; 
lean_dec(x_322);
lean_dec(x_318);
lean_dec(x_87);
lean_dec(x_11);
x_334 = lean_ctor_get(x_20, 2);
lean_inc(x_334);
x_335 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(x_334);
lean_dec(x_334);
if (x_335 == 0)
{
lean_object* x_336; lean_object* x_337; 
lean_dec(x_333);
lean_dec(x_332);
lean_dec(x_324);
lean_free_object(x_82);
lean_dec(x_80);
x_336 = lean_box(0);
x_337 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5(x_2, x_314, x_3, x_331, x_336, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_329);
return x_337;
}
else
{
if (lean_obj_tag(x_80) == 1)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_338 = lean_ctor_get(x_80, 0);
lean_inc(x_338);
lean_dec(x_80);
x_339 = lean_ctor_get(x_18, 2);
lean_inc(x_339);
lean_inc(x_338);
x_340 = l_Lean_LocalContext_getRoundtrippingUserName_x3f(x_339, x_338);
if (lean_obj_tag(x_340) == 0)
{
lean_dec(x_338);
lean_dec(x_332);
lean_dec(x_331);
lean_dec(x_324);
lean_dec(x_314);
lean_free_object(x_82);
lean_dec(x_3);
lean_dec(x_2);
x_47 = x_21;
x_48 = x_19;
x_49 = x_15;
x_50 = x_329;
x_51 = x_333;
x_52 = x_18;
x_53 = x_16;
x_54 = x_20;
x_55 = x_17;
x_56 = x_14;
goto block_59;
}
else
{
lean_dec(x_340);
if (x_12 == 0)
{
lean_dec(x_338);
lean_dec(x_332);
lean_dec(x_331);
lean_dec(x_324);
lean_dec(x_314);
lean_free_object(x_82);
lean_dec(x_3);
lean_dec(x_2);
x_47 = x_21;
x_48 = x_19;
x_49 = x_15;
x_50 = x_329;
x_51 = x_333;
x_52 = x_18;
x_53 = x_16;
x_54 = x_20;
x_55 = x_17;
x_56 = x_14;
goto block_59;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
lean_dec(x_333);
x_341 = lean_ctor_get(x_20, 5);
lean_inc(x_341);
x_342 = l_linter_unnecessarySimpa;
x_343 = lean_mk_string_unchecked("try 'simp at ", 13, 13);
x_344 = l_Lean_stringToMessageData(x_343);
lean_dec(x_343);
x_345 = l_Lean_Expr_fvar___override(x_338);
x_346 = l_Lean_MessageData_ofExpr(x_345);
lean_inc(x_346);
if (lean_is_scalar(x_332)) {
 x_347 = lean_alloc_ctor(7, 2, 0);
} else {
 x_347 = x_332;
 lean_ctor_set_tag(x_347, 7);
}
lean_ctor_set(x_347, 0, x_344);
lean_ctor_set(x_347, 1, x_346);
x_348 = lean_mk_string_unchecked("' instead of 'simpa using ", 26, 26);
x_349 = l_Lean_stringToMessageData(x_348);
lean_dec(x_348);
if (lean_is_scalar(x_324)) {
 x_350 = lean_alloc_ctor(7, 2, 0);
} else {
 x_350 = x_324;
 lean_ctor_set_tag(x_350, 7);
}
lean_ctor_set(x_350, 0, x_347);
lean_ctor_set(x_350, 1, x_349);
x_351 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_351, 0, x_350);
lean_ctor_set(x_351, 1, x_346);
x_352 = lean_mk_string_unchecked("'", 1, 1);
x_353 = l_Lean_stringToMessageData(x_352);
lean_dec(x_352);
lean_ctor_set_tag(x_82, 7);
lean_ctor_set(x_82, 1, x_353);
lean_ctor_set(x_82, 0, x_351);
lean_inc(x_20);
x_354 = l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1(x_342, x_341, x_82, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_329);
lean_dec(x_341);
x_355 = lean_ctor_get(x_354, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_354, 1);
lean_inc(x_356);
lean_dec(x_354);
x_357 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5(x_2, x_314, x_3, x_331, x_355, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_356);
lean_dec(x_355);
return x_357;
}
}
}
else
{
lean_object* x_358; lean_object* x_359; 
lean_dec(x_333);
lean_dec(x_332);
lean_dec(x_324);
lean_free_object(x_82);
lean_dec(x_80);
x_358 = lean_box(0);
x_359 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5(x_2, x_314, x_3, x_331, x_358, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_329);
return x_359;
}
}
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; uint8_t x_364; 
lean_dec(x_332);
lean_dec(x_331);
lean_dec(x_324);
lean_dec(x_314);
lean_free_object(x_82);
lean_dec(x_3);
lean_dec(x_2);
x_360 = lean_ctor_get(x_330, 0);
lean_inc(x_360);
lean_dec(x_330);
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_360, 1);
lean_inc(x_362);
lean_dec(x_360);
x_363 = lean_array_get_size(x_361);
x_364 = lean_nat_dec_lt(x_13, x_363);
lean_dec(x_363);
if (x_364 == 0)
{
lean_dec(x_361);
x_88 = x_21;
x_89 = x_362;
x_90 = x_15;
x_91 = x_19;
x_92 = x_333;
x_93 = x_329;
x_94 = x_18;
x_95 = x_16;
x_96 = x_17;
x_97 = x_14;
x_98 = x_20;
x_99 = x_318;
x_100 = x_322;
goto block_152;
}
else
{
lean_object* x_365; 
lean_dec(x_322);
x_365 = lean_array_fget(x_361, x_13);
lean_dec(x_361);
x_88 = x_21;
x_89 = x_362;
x_90 = x_15;
x_91 = x_19;
x_92 = x_333;
x_93 = x_329;
x_94 = x_18;
x_95 = x_16;
x_96 = x_17;
x_97 = x_14;
x_98 = x_20;
x_99 = x_318;
x_100 = x_365;
goto block_152;
}
}
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
lean_dec(x_324);
lean_dec(x_322);
lean_dec(x_318);
lean_dec(x_314);
lean_dec(x_87);
lean_free_object(x_82);
lean_dec(x_80);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_366 = lean_ctor_get(x_327, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_327, 1);
lean_inc(x_367);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 lean_ctor_release(x_327, 1);
 x_368 = x_327;
} else {
 lean_dec_ref(x_327);
 x_368 = lean_box(0);
}
if (lean_is_scalar(x_368)) {
 x_369 = lean_alloc_ctor(1, 2, 0);
} else {
 x_369 = x_368;
}
lean_ctor_set(x_369, 0, x_366);
lean_ctor_set(x_369, 1, x_367);
return x_369;
}
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
lean_dec(x_318);
lean_dec(x_314);
lean_dec(x_87);
lean_free_object(x_82);
lean_dec(x_80);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_370 = lean_ctor_get(x_319, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_319, 1);
lean_inc(x_371);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 lean_ctor_release(x_319, 1);
 x_372 = x_319;
} else {
 lean_dec_ref(x_319);
 x_372 = lean_box(0);
}
if (lean_is_scalar(x_372)) {
 x_373 = lean_alloc_ctor(1, 2, 0);
} else {
 x_373 = x_372;
}
lean_ctor_set(x_373, 0, x_370);
lean_ctor_set(x_373, 1, x_371);
return x_373;
}
}
}
else
{
uint8_t x_374; 
lean_dec(x_171);
lean_dec(x_87);
lean_free_object(x_82);
lean_dec(x_80);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_374 = !lean_is_exclusive(x_173);
if (x_374 == 0)
{
return x_173;
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_375 = lean_ctor_get(x_173, 0);
x_376 = lean_ctor_get(x_173, 1);
lean_inc(x_376);
lean_inc(x_375);
lean_dec(x_173);
x_377 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_377, 0, x_375);
lean_ctor_set(x_377, 1, x_376);
return x_377;
}
}
}
else
{
uint8_t x_378; 
lean_dec(x_87);
lean_free_object(x_82);
lean_dec(x_80);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_378 = !lean_is_exclusive(x_170);
if (x_378 == 0)
{
return x_170;
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_379 = lean_ctor_get(x_170, 0);
x_380 = lean_ctor_get(x_170, 1);
lean_inc(x_380);
lean_inc(x_379);
lean_dec(x_170);
x_381 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_381, 0, x_379);
lean_ctor_set(x_381, 1, x_380);
return x_381;
}
}
}
block_152:
{
lean_object* x_101; uint8_t x_102; 
x_101 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_99, x_98, x_88, x_93);
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_101, 0);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_88);
lean_inc(x_98);
lean_inc(x_91);
lean_inc(x_103);
x_105 = l_Lean_MVarId_rename(x_89, x_100, x_103, x_94, x_91, x_98, x_88, x_104);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_box(0);
lean_inc(x_106);
lean_ctor_set_tag(x_101, 1);
lean_ctor_set(x_101, 1, x_108);
lean_ctor_set(x_101, 0, x_106);
x_109 = l_Lean_Elab_Tactic_setGoals___redArg(x_101, x_90, x_107);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
x_111 = lean_box(x_10);
x_112 = lean_box(x_9);
x_113 = lean_box(x_12);
lean_inc(x_106);
x_114 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___boxed), 18, 9);
lean_closure_set(x_114, 0, x_106);
lean_closure_set(x_114, 1, x_103);
lean_closure_set(x_114, 2, x_111);
lean_closure_set(x_114, 3, x_112);
lean_closure_set(x_114, 4, x_80);
lean_closure_set(x_114, 5, x_87);
lean_closure_set(x_114, 6, x_11);
lean_closure_set(x_114, 7, x_78);
lean_closure_set(x_114, 8, x_113);
lean_inc(x_88);
lean_inc(x_98);
lean_inc(x_91);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_90);
lean_inc(x_97);
x_115 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_withMainContext_spec__0___redArg(x_106, x_114, x_97, x_90, x_95, x_96, x_94, x_91, x_98, x_88, x_110);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_apply_10(x_92, x_116, x_97, x_90, x_95, x_96, x_94, x_91, x_98, x_88, x_117);
return x_118;
}
else
{
uint8_t x_119; 
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_88);
x_119 = !lean_is_exclusive(x_115);
if (x_119 == 0)
{
return x_115;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_115, 0);
x_121 = lean_ctor_get(x_115, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_115);
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
lean_free_object(x_101);
lean_dec(x_103);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_80);
lean_dec(x_11);
x_123 = !lean_is_exclusive(x_105);
if (x_123 == 0)
{
return x_105;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_105, 0);
x_125 = lean_ctor_get(x_105, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_105);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_101, 0);
x_128 = lean_ctor_get(x_101, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_101);
lean_inc(x_88);
lean_inc(x_98);
lean_inc(x_91);
lean_inc(x_127);
x_129 = l_Lean_MVarId_rename(x_89, x_100, x_127, x_94, x_91, x_98, x_88, x_128);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_box(0);
lean_inc(x_130);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_132);
x_134 = l_Lean_Elab_Tactic_setGoals___redArg(x_133, x_90, x_131);
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
lean_dec(x_134);
x_136 = lean_box(x_10);
x_137 = lean_box(x_9);
x_138 = lean_box(x_12);
lean_inc(x_130);
x_139 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___boxed), 18, 9);
lean_closure_set(x_139, 0, x_130);
lean_closure_set(x_139, 1, x_127);
lean_closure_set(x_139, 2, x_136);
lean_closure_set(x_139, 3, x_137);
lean_closure_set(x_139, 4, x_80);
lean_closure_set(x_139, 5, x_87);
lean_closure_set(x_139, 6, x_11);
lean_closure_set(x_139, 7, x_78);
lean_closure_set(x_139, 8, x_138);
lean_inc(x_88);
lean_inc(x_98);
lean_inc(x_91);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_90);
lean_inc(x_97);
x_140 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_withMainContext_spec__0___redArg(x_130, x_139, x_97, x_90, x_95, x_96, x_94, x_91, x_98, x_88, x_135);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = lean_apply_10(x_92, x_141, x_97, x_90, x_95, x_96, x_94, x_91, x_98, x_88, x_142);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_88);
x_144 = lean_ctor_get(x_140, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_140, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_146 = x_140;
} else {
 lean_dec_ref(x_140);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_127);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_80);
lean_dec(x_11);
x_148 = lean_ctor_get(x_129, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_129, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_150 = x_129;
} else {
 lean_dec_ref(x_129);
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
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; uint8_t x_427; 
x_382 = lean_ctor_get(x_82, 0);
x_383 = lean_ctor_get(x_82, 1);
lean_inc(x_383);
lean_inc(x_382);
lean_dec(x_82);
x_384 = lean_ctor_get(x_76, 0);
lean_inc(x_384);
lean_dec(x_76);
x_385 = lean_ctor_get(x_384, 2);
lean_inc(x_385);
lean_dec(x_384);
x_427 = lean_unbox(x_382);
lean_dec(x_382);
if (x_427 == 0)
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; 
lean_dec(x_385);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_428 = lean_mk_string_unchecked("occurs check failed, expression", 31, 31);
x_429 = l_Lean_stringToMessageData(x_428);
lean_dec(x_428);
x_430 = l_Lean_indentExpr(x_80);
x_431 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_431, 0, x_429);
lean_ctor_set(x_431, 1, x_430);
x_432 = lean_mk_string_unchecked("\ncontains the goal ", 19, 19);
x_433 = l_Lean_stringToMessageData(x_432);
lean_dec(x_432);
lean_ctor_set_tag(x_74, 7);
lean_ctor_set(x_74, 1, x_433);
lean_ctor_set(x_74, 0, x_431);
x_434 = l_Lean_Expr_mvar___override(x_2);
x_435 = l_Lean_MessageData_ofExpr(x_434);
x_436 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_436, 0, x_74);
lean_ctor_set(x_436, 1, x_435);
x_437 = lean_mk_string_unchecked("", 0, 0);
x_438 = l_Lean_stringToMessageData(x_437);
lean_dec(x_437);
x_439 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_439, 0, x_436);
lean_ctor_set(x_439, 1, x_438);
x_440 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_439, x_18, x_19, x_20, x_21, x_383);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_441 = lean_ctor_get(x_440, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_440, 1);
lean_inc(x_442);
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 lean_ctor_release(x_440, 1);
 x_443 = x_440;
} else {
 lean_dec_ref(x_440);
 x_443 = lean_box(0);
}
if (lean_is_scalar(x_443)) {
 x_444 = lean_alloc_ctor(1, 2, 0);
} else {
 x_444 = x_443;
}
lean_ctor_set(x_444, 0, x_441);
lean_ctor_set(x_444, 1, x_442);
return x_444;
}
else
{
lean_object* x_445; 
lean_free_object(x_74);
lean_inc(x_2);
x_445 = l_Lean_MVarId_getType(x_2, x_18, x_19, x_20, x_21, x_383);
if (lean_obj_tag(x_445) == 0)
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_446 = lean_ctor_get(x_445, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_445, 1);
lean_inc(x_447);
lean_dec(x_445);
lean_inc(x_2);
x_448 = l_Lean_MVarId_getTag(x_2, x_18, x_19, x_20, x_21, x_447);
if (lean_obj_tag(x_448) == 0)
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_449 = lean_ctor_get(x_448, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_448, 1);
lean_inc(x_450);
lean_dec(x_448);
lean_inc(x_18);
x_451 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_446, x_449, x_18, x_19, x_20, x_21, x_450);
x_452 = lean_ctor_get(x_451, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_451, 1);
lean_inc(x_453);
if (lean_is_exclusive(x_451)) {
 lean_ctor_release(x_451, 0);
 lean_ctor_release(x_451, 1);
 x_454 = x_451;
} else {
 lean_dec_ref(x_451);
 x_454 = lean_box(0);
}
x_455 = l_Lean_Expr_mvarId_x21(x_452);
x_456 = lean_mk_string_unchecked("h", 1, 1);
x_457 = l_Lean_Name_mkStr1(x_456);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_80);
lean_inc(x_457);
x_458 = l_Lean_MVarId_note(x_455, x_457, x_80, x_78, x_18, x_19, x_20, x_21, x_453);
if (lean_obj_tag(x_458) == 0)
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_459 = lean_ctor_get(x_458, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_458, 1);
lean_inc(x_460);
lean_dec(x_458);
x_461 = lean_ctor_get(x_459, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_459, 1);
lean_inc(x_462);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 x_463 = x_459;
} else {
 lean_dec_ref(x_459);
 x_463 = lean_box(0);
}
x_464 = lean_mk_empty_array_with_capacity(x_5);
lean_inc(x_461);
x_465 = lean_array_push(x_464, x_461);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_466 = l_Lean_Meta_simpGoal(x_462, x_6, x_7, x_8, x_9, x_465, x_4, x_18, x_19, x_20, x_21, x_460);
if (lean_obj_tag(x_466) == 0)
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; 
x_467 = lean_ctor_get(x_466, 0);
lean_inc(x_467);
x_468 = lean_ctor_get(x_466, 1);
lean_inc(x_468);
lean_dec(x_466);
x_469 = lean_ctor_get(x_467, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_467, 1);
lean_inc(x_470);
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 lean_ctor_release(x_467, 1);
 x_471 = x_467;
} else {
 lean_dec_ref(x_467);
 x_471 = lean_box(0);
}
lean_inc(x_470);
lean_inc(x_3);
lean_inc(x_452);
lean_inc(x_2);
x_472 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___boxed), 14, 4);
lean_closure_set(x_472, 0, x_2);
lean_closure_set(x_472, 1, x_452);
lean_closure_set(x_472, 2, x_3);
lean_closure_set(x_472, 3, x_470);
if (lean_obj_tag(x_469) == 0)
{
lean_object* x_473; uint8_t x_474; 
lean_dec(x_461);
lean_dec(x_457);
lean_dec(x_385);
lean_dec(x_11);
x_473 = lean_ctor_get(x_20, 2);
lean_inc(x_473);
x_474 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(x_473);
lean_dec(x_473);
if (x_474 == 0)
{
lean_object* x_475; lean_object* x_476; 
lean_dec(x_472);
lean_dec(x_471);
lean_dec(x_463);
lean_dec(x_454);
lean_dec(x_80);
x_475 = lean_box(0);
x_476 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5(x_2, x_452, x_3, x_470, x_475, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_468);
return x_476;
}
else
{
if (lean_obj_tag(x_80) == 1)
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; 
x_477 = lean_ctor_get(x_80, 0);
lean_inc(x_477);
lean_dec(x_80);
x_478 = lean_ctor_get(x_18, 2);
lean_inc(x_478);
lean_inc(x_477);
x_479 = l_Lean_LocalContext_getRoundtrippingUserName_x3f(x_478, x_477);
if (lean_obj_tag(x_479) == 0)
{
lean_dec(x_477);
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_463);
lean_dec(x_454);
lean_dec(x_452);
lean_dec(x_3);
lean_dec(x_2);
x_47 = x_21;
x_48 = x_19;
x_49 = x_15;
x_50 = x_468;
x_51 = x_472;
x_52 = x_18;
x_53 = x_16;
x_54 = x_20;
x_55 = x_17;
x_56 = x_14;
goto block_59;
}
else
{
lean_dec(x_479);
if (x_12 == 0)
{
lean_dec(x_477);
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_463);
lean_dec(x_454);
lean_dec(x_452);
lean_dec(x_3);
lean_dec(x_2);
x_47 = x_21;
x_48 = x_19;
x_49 = x_15;
x_50 = x_468;
x_51 = x_472;
x_52 = x_18;
x_53 = x_16;
x_54 = x_20;
x_55 = x_17;
x_56 = x_14;
goto block_59;
}
else
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; 
lean_dec(x_472);
x_480 = lean_ctor_get(x_20, 5);
lean_inc(x_480);
x_481 = l_linter_unnecessarySimpa;
x_482 = lean_mk_string_unchecked("try 'simp at ", 13, 13);
x_483 = l_Lean_stringToMessageData(x_482);
lean_dec(x_482);
x_484 = l_Lean_Expr_fvar___override(x_477);
x_485 = l_Lean_MessageData_ofExpr(x_484);
lean_inc(x_485);
if (lean_is_scalar(x_471)) {
 x_486 = lean_alloc_ctor(7, 2, 0);
} else {
 x_486 = x_471;
 lean_ctor_set_tag(x_486, 7);
}
lean_ctor_set(x_486, 0, x_483);
lean_ctor_set(x_486, 1, x_485);
x_487 = lean_mk_string_unchecked("' instead of 'simpa using ", 26, 26);
x_488 = l_Lean_stringToMessageData(x_487);
lean_dec(x_487);
if (lean_is_scalar(x_463)) {
 x_489 = lean_alloc_ctor(7, 2, 0);
} else {
 x_489 = x_463;
 lean_ctor_set_tag(x_489, 7);
}
lean_ctor_set(x_489, 0, x_486);
lean_ctor_set(x_489, 1, x_488);
if (lean_is_scalar(x_454)) {
 x_490 = lean_alloc_ctor(7, 2, 0);
} else {
 x_490 = x_454;
 lean_ctor_set_tag(x_490, 7);
}
lean_ctor_set(x_490, 0, x_489);
lean_ctor_set(x_490, 1, x_485);
x_491 = lean_mk_string_unchecked("'", 1, 1);
x_492 = l_Lean_stringToMessageData(x_491);
lean_dec(x_491);
x_493 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_493, 0, x_490);
lean_ctor_set(x_493, 1, x_492);
lean_inc(x_20);
x_494 = l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1(x_481, x_480, x_493, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_468);
lean_dec(x_480);
x_495 = lean_ctor_get(x_494, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_494, 1);
lean_inc(x_496);
lean_dec(x_494);
x_497 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5(x_2, x_452, x_3, x_470, x_495, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_496);
lean_dec(x_495);
return x_497;
}
}
}
else
{
lean_object* x_498; lean_object* x_499; 
lean_dec(x_472);
lean_dec(x_471);
lean_dec(x_463);
lean_dec(x_454);
lean_dec(x_80);
x_498 = lean_box(0);
x_499 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5(x_2, x_452, x_3, x_470, x_498, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_468);
return x_499;
}
}
}
else
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; uint8_t x_504; 
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_463);
lean_dec(x_454);
lean_dec(x_452);
lean_dec(x_3);
lean_dec(x_2);
x_500 = lean_ctor_get(x_469, 0);
lean_inc(x_500);
lean_dec(x_469);
x_501 = lean_ctor_get(x_500, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_500, 1);
lean_inc(x_502);
lean_dec(x_500);
x_503 = lean_array_get_size(x_501);
x_504 = lean_nat_dec_lt(x_13, x_503);
lean_dec(x_503);
if (x_504 == 0)
{
lean_dec(x_501);
x_386 = x_21;
x_387 = x_502;
x_388 = x_15;
x_389 = x_19;
x_390 = x_472;
x_391 = x_468;
x_392 = x_18;
x_393 = x_16;
x_394 = x_17;
x_395 = x_14;
x_396 = x_20;
x_397 = x_457;
x_398 = x_461;
goto block_426;
}
else
{
lean_object* x_505; 
lean_dec(x_461);
x_505 = lean_array_fget(x_501, x_13);
lean_dec(x_501);
x_386 = x_21;
x_387 = x_502;
x_388 = x_15;
x_389 = x_19;
x_390 = x_472;
x_391 = x_468;
x_392 = x_18;
x_393 = x_16;
x_394 = x_17;
x_395 = x_14;
x_396 = x_20;
x_397 = x_457;
x_398 = x_505;
goto block_426;
}
}
}
else
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; 
lean_dec(x_463);
lean_dec(x_461);
lean_dec(x_457);
lean_dec(x_454);
lean_dec(x_452);
lean_dec(x_385);
lean_dec(x_80);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_506 = lean_ctor_get(x_466, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_466, 1);
lean_inc(x_507);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 lean_ctor_release(x_466, 1);
 x_508 = x_466;
} else {
 lean_dec_ref(x_466);
 x_508 = lean_box(0);
}
if (lean_is_scalar(x_508)) {
 x_509 = lean_alloc_ctor(1, 2, 0);
} else {
 x_509 = x_508;
}
lean_ctor_set(x_509, 0, x_506);
lean_ctor_set(x_509, 1, x_507);
return x_509;
}
}
else
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; 
lean_dec(x_457);
lean_dec(x_454);
lean_dec(x_452);
lean_dec(x_385);
lean_dec(x_80);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_510 = lean_ctor_get(x_458, 0);
lean_inc(x_510);
x_511 = lean_ctor_get(x_458, 1);
lean_inc(x_511);
if (lean_is_exclusive(x_458)) {
 lean_ctor_release(x_458, 0);
 lean_ctor_release(x_458, 1);
 x_512 = x_458;
} else {
 lean_dec_ref(x_458);
 x_512 = lean_box(0);
}
if (lean_is_scalar(x_512)) {
 x_513 = lean_alloc_ctor(1, 2, 0);
} else {
 x_513 = x_512;
}
lean_ctor_set(x_513, 0, x_510);
lean_ctor_set(x_513, 1, x_511);
return x_513;
}
}
else
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; 
lean_dec(x_446);
lean_dec(x_385);
lean_dec(x_80);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_514 = lean_ctor_get(x_448, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_448, 1);
lean_inc(x_515);
if (lean_is_exclusive(x_448)) {
 lean_ctor_release(x_448, 0);
 lean_ctor_release(x_448, 1);
 x_516 = x_448;
} else {
 lean_dec_ref(x_448);
 x_516 = lean_box(0);
}
if (lean_is_scalar(x_516)) {
 x_517 = lean_alloc_ctor(1, 2, 0);
} else {
 x_517 = x_516;
}
lean_ctor_set(x_517, 0, x_514);
lean_ctor_set(x_517, 1, x_515);
return x_517;
}
}
else
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; 
lean_dec(x_385);
lean_dec(x_80);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_518 = lean_ctor_get(x_445, 0);
lean_inc(x_518);
x_519 = lean_ctor_get(x_445, 1);
lean_inc(x_519);
if (lean_is_exclusive(x_445)) {
 lean_ctor_release(x_445, 0);
 lean_ctor_release(x_445, 1);
 x_520 = x_445;
} else {
 lean_dec_ref(x_445);
 x_520 = lean_box(0);
}
if (lean_is_scalar(x_520)) {
 x_521 = lean_alloc_ctor(1, 2, 0);
} else {
 x_521 = x_520;
}
lean_ctor_set(x_521, 0, x_518);
lean_ctor_set(x_521, 1, x_519);
return x_521;
}
}
block_426:
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_399 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_397, x_396, x_386, x_391);
x_400 = lean_ctor_get(x_399, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_399, 1);
lean_inc(x_401);
if (lean_is_exclusive(x_399)) {
 lean_ctor_release(x_399, 0);
 lean_ctor_release(x_399, 1);
 x_402 = x_399;
} else {
 lean_dec_ref(x_399);
 x_402 = lean_box(0);
}
lean_inc(x_386);
lean_inc(x_396);
lean_inc(x_389);
lean_inc(x_400);
x_403 = l_Lean_MVarId_rename(x_387, x_398, x_400, x_392, x_389, x_396, x_386, x_401);
if (lean_obj_tag(x_403) == 0)
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_403, 1);
lean_inc(x_405);
lean_dec(x_403);
x_406 = lean_box(0);
lean_inc(x_404);
if (lean_is_scalar(x_402)) {
 x_407 = lean_alloc_ctor(1, 2, 0);
} else {
 x_407 = x_402;
 lean_ctor_set_tag(x_407, 1);
}
lean_ctor_set(x_407, 0, x_404);
lean_ctor_set(x_407, 1, x_406);
x_408 = l_Lean_Elab_Tactic_setGoals___redArg(x_407, x_388, x_405);
x_409 = lean_ctor_get(x_408, 1);
lean_inc(x_409);
lean_dec(x_408);
x_410 = lean_box(x_10);
x_411 = lean_box(x_9);
x_412 = lean_box(x_12);
lean_inc(x_404);
x_413 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___boxed), 18, 9);
lean_closure_set(x_413, 0, x_404);
lean_closure_set(x_413, 1, x_400);
lean_closure_set(x_413, 2, x_410);
lean_closure_set(x_413, 3, x_411);
lean_closure_set(x_413, 4, x_80);
lean_closure_set(x_413, 5, x_385);
lean_closure_set(x_413, 6, x_11);
lean_closure_set(x_413, 7, x_78);
lean_closure_set(x_413, 8, x_412);
lean_inc(x_386);
lean_inc(x_396);
lean_inc(x_389);
lean_inc(x_394);
lean_inc(x_393);
lean_inc(x_388);
lean_inc(x_395);
x_414 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_withMainContext_spec__0___redArg(x_404, x_413, x_395, x_388, x_393, x_394, x_392, x_389, x_396, x_386, x_409);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_414, 1);
lean_inc(x_416);
lean_dec(x_414);
x_417 = lean_apply_10(x_390, x_415, x_395, x_388, x_393, x_394, x_392, x_389, x_396, x_386, x_416);
return x_417;
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
lean_dec(x_396);
lean_dec(x_395);
lean_dec(x_394);
lean_dec(x_393);
lean_dec(x_392);
lean_dec(x_390);
lean_dec(x_389);
lean_dec(x_388);
lean_dec(x_386);
x_418 = lean_ctor_get(x_414, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_414, 1);
lean_inc(x_419);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 x_420 = x_414;
} else {
 lean_dec_ref(x_414);
 x_420 = lean_box(0);
}
if (lean_is_scalar(x_420)) {
 x_421 = lean_alloc_ctor(1, 2, 0);
} else {
 x_421 = x_420;
}
lean_ctor_set(x_421, 0, x_418);
lean_ctor_set(x_421, 1, x_419);
return x_421;
}
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
lean_dec(x_402);
lean_dec(x_400);
lean_dec(x_396);
lean_dec(x_395);
lean_dec(x_394);
lean_dec(x_393);
lean_dec(x_392);
lean_dec(x_390);
lean_dec(x_389);
lean_dec(x_388);
lean_dec(x_386);
lean_dec(x_385);
lean_dec(x_80);
lean_dec(x_11);
x_422 = lean_ctor_get(x_403, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_403, 1);
lean_inc(x_423);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 x_424 = x_403;
} else {
 lean_dec_ref(x_403);
 x_424 = lean_box(0);
}
if (lean_is_scalar(x_424)) {
 x_425 = lean_alloc_ctor(1, 2, 0);
} else {
 x_425 = x_424;
}
lean_ctor_set(x_425, 0, x_422);
lean_ctor_set(x_425, 1, x_423);
return x_425;
}
}
}
}
else
{
uint8_t x_522; 
lean_free_object(x_74);
lean_dec(x_76);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_522 = !lean_is_exclusive(x_79);
if (x_522 == 0)
{
return x_79;
}
else
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; 
x_523 = lean_ctor_get(x_79, 0);
x_524 = lean_ctor_get(x_79, 1);
lean_inc(x_524);
lean_inc(x_523);
lean_dec(x_79);
x_525 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_525, 0, x_523);
lean_ctor_set(x_525, 1, x_524);
return x_525;
}
}
}
else
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; 
x_526 = lean_ctor_get(x_74, 0);
x_527 = lean_ctor_get(x_74, 1);
lean_inc(x_527);
lean_inc(x_526);
lean_dec(x_74);
x_528 = lean_box(0);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_529 = l_Lean_Elab_Tactic_elabTerm(x_73, x_528, x_10, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_527);
if (lean_obj_tag(x_529) == 0)
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; uint8_t x_579; 
x_530 = lean_ctor_get(x_529, 0);
lean_inc(x_530);
x_531 = lean_ctor_get(x_529, 1);
lean_inc(x_531);
lean_dec(x_529);
lean_inc(x_530);
x_532 = l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3(x_2, x_530, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_531);
x_533 = lean_ctor_get(x_532, 0);
lean_inc(x_533);
x_534 = lean_ctor_get(x_532, 1);
lean_inc(x_534);
if (lean_is_exclusive(x_532)) {
 lean_ctor_release(x_532, 0);
 lean_ctor_release(x_532, 1);
 x_535 = x_532;
} else {
 lean_dec_ref(x_532);
 x_535 = lean_box(0);
}
x_536 = lean_ctor_get(x_526, 0);
lean_inc(x_536);
lean_dec(x_526);
x_537 = lean_ctor_get(x_536, 2);
lean_inc(x_537);
lean_dec(x_536);
x_579 = lean_unbox(x_533);
lean_dec(x_533);
if (x_579 == 0)
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; 
lean_dec(x_537);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_580 = lean_mk_string_unchecked("occurs check failed, expression", 31, 31);
x_581 = l_Lean_stringToMessageData(x_580);
lean_dec(x_580);
x_582 = l_Lean_indentExpr(x_530);
if (lean_is_scalar(x_535)) {
 x_583 = lean_alloc_ctor(7, 2, 0);
} else {
 x_583 = x_535;
 lean_ctor_set_tag(x_583, 7);
}
lean_ctor_set(x_583, 0, x_581);
lean_ctor_set(x_583, 1, x_582);
x_584 = lean_mk_string_unchecked("\ncontains the goal ", 19, 19);
x_585 = l_Lean_stringToMessageData(x_584);
lean_dec(x_584);
x_586 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_586, 0, x_583);
lean_ctor_set(x_586, 1, x_585);
x_587 = l_Lean_Expr_mvar___override(x_2);
x_588 = l_Lean_MessageData_ofExpr(x_587);
x_589 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_589, 0, x_586);
lean_ctor_set(x_589, 1, x_588);
x_590 = lean_mk_string_unchecked("", 0, 0);
x_591 = l_Lean_stringToMessageData(x_590);
lean_dec(x_590);
x_592 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_592, 0, x_589);
lean_ctor_set(x_592, 1, x_591);
x_593 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_592, x_18, x_19, x_20, x_21, x_534);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_594 = lean_ctor_get(x_593, 0);
lean_inc(x_594);
x_595 = lean_ctor_get(x_593, 1);
lean_inc(x_595);
if (lean_is_exclusive(x_593)) {
 lean_ctor_release(x_593, 0);
 lean_ctor_release(x_593, 1);
 x_596 = x_593;
} else {
 lean_dec_ref(x_593);
 x_596 = lean_box(0);
}
if (lean_is_scalar(x_596)) {
 x_597 = lean_alloc_ctor(1, 2, 0);
} else {
 x_597 = x_596;
}
lean_ctor_set(x_597, 0, x_594);
lean_ctor_set(x_597, 1, x_595);
return x_597;
}
else
{
lean_object* x_598; 
lean_inc(x_2);
x_598 = l_Lean_MVarId_getType(x_2, x_18, x_19, x_20, x_21, x_534);
if (lean_obj_tag(x_598) == 0)
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; 
x_599 = lean_ctor_get(x_598, 0);
lean_inc(x_599);
x_600 = lean_ctor_get(x_598, 1);
lean_inc(x_600);
lean_dec(x_598);
lean_inc(x_2);
x_601 = l_Lean_MVarId_getTag(x_2, x_18, x_19, x_20, x_21, x_600);
if (lean_obj_tag(x_601) == 0)
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; 
x_602 = lean_ctor_get(x_601, 0);
lean_inc(x_602);
x_603 = lean_ctor_get(x_601, 1);
lean_inc(x_603);
lean_dec(x_601);
lean_inc(x_18);
x_604 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_599, x_602, x_18, x_19, x_20, x_21, x_603);
x_605 = lean_ctor_get(x_604, 0);
lean_inc(x_605);
x_606 = lean_ctor_get(x_604, 1);
lean_inc(x_606);
if (lean_is_exclusive(x_604)) {
 lean_ctor_release(x_604, 0);
 lean_ctor_release(x_604, 1);
 x_607 = x_604;
} else {
 lean_dec_ref(x_604);
 x_607 = lean_box(0);
}
x_608 = l_Lean_Expr_mvarId_x21(x_605);
x_609 = lean_mk_string_unchecked("h", 1, 1);
x_610 = l_Lean_Name_mkStr1(x_609);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_530);
lean_inc(x_610);
x_611 = l_Lean_MVarId_note(x_608, x_610, x_530, x_528, x_18, x_19, x_20, x_21, x_606);
if (lean_obj_tag(x_611) == 0)
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; 
x_612 = lean_ctor_get(x_611, 0);
lean_inc(x_612);
x_613 = lean_ctor_get(x_611, 1);
lean_inc(x_613);
lean_dec(x_611);
x_614 = lean_ctor_get(x_612, 0);
lean_inc(x_614);
x_615 = lean_ctor_get(x_612, 1);
lean_inc(x_615);
if (lean_is_exclusive(x_612)) {
 lean_ctor_release(x_612, 0);
 lean_ctor_release(x_612, 1);
 x_616 = x_612;
} else {
 lean_dec_ref(x_612);
 x_616 = lean_box(0);
}
x_617 = lean_mk_empty_array_with_capacity(x_5);
lean_inc(x_614);
x_618 = lean_array_push(x_617, x_614);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_619 = l_Lean_Meta_simpGoal(x_615, x_6, x_7, x_8, x_9, x_618, x_4, x_18, x_19, x_20, x_21, x_613);
if (lean_obj_tag(x_619) == 0)
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; 
x_620 = lean_ctor_get(x_619, 0);
lean_inc(x_620);
x_621 = lean_ctor_get(x_619, 1);
lean_inc(x_621);
lean_dec(x_619);
x_622 = lean_ctor_get(x_620, 0);
lean_inc(x_622);
x_623 = lean_ctor_get(x_620, 1);
lean_inc(x_623);
if (lean_is_exclusive(x_620)) {
 lean_ctor_release(x_620, 0);
 lean_ctor_release(x_620, 1);
 x_624 = x_620;
} else {
 lean_dec_ref(x_620);
 x_624 = lean_box(0);
}
lean_inc(x_623);
lean_inc(x_3);
lean_inc(x_605);
lean_inc(x_2);
x_625 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___boxed), 14, 4);
lean_closure_set(x_625, 0, x_2);
lean_closure_set(x_625, 1, x_605);
lean_closure_set(x_625, 2, x_3);
lean_closure_set(x_625, 3, x_623);
if (lean_obj_tag(x_622) == 0)
{
lean_object* x_626; uint8_t x_627; 
lean_dec(x_614);
lean_dec(x_610);
lean_dec(x_537);
lean_dec(x_11);
x_626 = lean_ctor_get(x_20, 2);
lean_inc(x_626);
x_627 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(x_626);
lean_dec(x_626);
if (x_627 == 0)
{
lean_object* x_628; lean_object* x_629; 
lean_dec(x_625);
lean_dec(x_624);
lean_dec(x_616);
lean_dec(x_607);
lean_dec(x_535);
lean_dec(x_530);
x_628 = lean_box(0);
x_629 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5(x_2, x_605, x_3, x_623, x_628, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_621);
return x_629;
}
else
{
if (lean_obj_tag(x_530) == 1)
{
lean_object* x_630; lean_object* x_631; lean_object* x_632; 
x_630 = lean_ctor_get(x_530, 0);
lean_inc(x_630);
lean_dec(x_530);
x_631 = lean_ctor_get(x_18, 2);
lean_inc(x_631);
lean_inc(x_630);
x_632 = l_Lean_LocalContext_getRoundtrippingUserName_x3f(x_631, x_630);
if (lean_obj_tag(x_632) == 0)
{
lean_dec(x_630);
lean_dec(x_624);
lean_dec(x_623);
lean_dec(x_616);
lean_dec(x_607);
lean_dec(x_605);
lean_dec(x_535);
lean_dec(x_3);
lean_dec(x_2);
x_47 = x_21;
x_48 = x_19;
x_49 = x_15;
x_50 = x_621;
x_51 = x_625;
x_52 = x_18;
x_53 = x_16;
x_54 = x_20;
x_55 = x_17;
x_56 = x_14;
goto block_59;
}
else
{
lean_dec(x_632);
if (x_12 == 0)
{
lean_dec(x_630);
lean_dec(x_624);
lean_dec(x_623);
lean_dec(x_616);
lean_dec(x_607);
lean_dec(x_605);
lean_dec(x_535);
lean_dec(x_3);
lean_dec(x_2);
x_47 = x_21;
x_48 = x_19;
x_49 = x_15;
x_50 = x_621;
x_51 = x_625;
x_52 = x_18;
x_53 = x_16;
x_54 = x_20;
x_55 = x_17;
x_56 = x_14;
goto block_59;
}
else
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; 
lean_dec(x_625);
x_633 = lean_ctor_get(x_20, 5);
lean_inc(x_633);
x_634 = l_linter_unnecessarySimpa;
x_635 = lean_mk_string_unchecked("try 'simp at ", 13, 13);
x_636 = l_Lean_stringToMessageData(x_635);
lean_dec(x_635);
x_637 = l_Lean_Expr_fvar___override(x_630);
x_638 = l_Lean_MessageData_ofExpr(x_637);
lean_inc(x_638);
if (lean_is_scalar(x_624)) {
 x_639 = lean_alloc_ctor(7, 2, 0);
} else {
 x_639 = x_624;
 lean_ctor_set_tag(x_639, 7);
}
lean_ctor_set(x_639, 0, x_636);
lean_ctor_set(x_639, 1, x_638);
x_640 = lean_mk_string_unchecked("' instead of 'simpa using ", 26, 26);
x_641 = l_Lean_stringToMessageData(x_640);
lean_dec(x_640);
if (lean_is_scalar(x_616)) {
 x_642 = lean_alloc_ctor(7, 2, 0);
} else {
 x_642 = x_616;
 lean_ctor_set_tag(x_642, 7);
}
lean_ctor_set(x_642, 0, x_639);
lean_ctor_set(x_642, 1, x_641);
if (lean_is_scalar(x_607)) {
 x_643 = lean_alloc_ctor(7, 2, 0);
} else {
 x_643 = x_607;
 lean_ctor_set_tag(x_643, 7);
}
lean_ctor_set(x_643, 0, x_642);
lean_ctor_set(x_643, 1, x_638);
x_644 = lean_mk_string_unchecked("'", 1, 1);
x_645 = l_Lean_stringToMessageData(x_644);
lean_dec(x_644);
if (lean_is_scalar(x_535)) {
 x_646 = lean_alloc_ctor(7, 2, 0);
} else {
 x_646 = x_535;
 lean_ctor_set_tag(x_646, 7);
}
lean_ctor_set(x_646, 0, x_643);
lean_ctor_set(x_646, 1, x_645);
lean_inc(x_20);
x_647 = l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1(x_634, x_633, x_646, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_621);
lean_dec(x_633);
x_648 = lean_ctor_get(x_647, 0);
lean_inc(x_648);
x_649 = lean_ctor_get(x_647, 1);
lean_inc(x_649);
lean_dec(x_647);
x_650 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5(x_2, x_605, x_3, x_623, x_648, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_649);
lean_dec(x_648);
return x_650;
}
}
}
else
{
lean_object* x_651; lean_object* x_652; 
lean_dec(x_625);
lean_dec(x_624);
lean_dec(x_616);
lean_dec(x_607);
lean_dec(x_535);
lean_dec(x_530);
x_651 = lean_box(0);
x_652 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5(x_2, x_605, x_3, x_623, x_651, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_621);
return x_652;
}
}
}
else
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; uint8_t x_657; 
lean_dec(x_624);
lean_dec(x_623);
lean_dec(x_616);
lean_dec(x_607);
lean_dec(x_605);
lean_dec(x_535);
lean_dec(x_3);
lean_dec(x_2);
x_653 = lean_ctor_get(x_622, 0);
lean_inc(x_653);
lean_dec(x_622);
x_654 = lean_ctor_get(x_653, 0);
lean_inc(x_654);
x_655 = lean_ctor_get(x_653, 1);
lean_inc(x_655);
lean_dec(x_653);
x_656 = lean_array_get_size(x_654);
x_657 = lean_nat_dec_lt(x_13, x_656);
lean_dec(x_656);
if (x_657 == 0)
{
lean_dec(x_654);
x_538 = x_21;
x_539 = x_655;
x_540 = x_15;
x_541 = x_19;
x_542 = x_625;
x_543 = x_621;
x_544 = x_18;
x_545 = x_16;
x_546 = x_17;
x_547 = x_14;
x_548 = x_20;
x_549 = x_610;
x_550 = x_614;
goto block_578;
}
else
{
lean_object* x_658; 
lean_dec(x_614);
x_658 = lean_array_fget(x_654, x_13);
lean_dec(x_654);
x_538 = x_21;
x_539 = x_655;
x_540 = x_15;
x_541 = x_19;
x_542 = x_625;
x_543 = x_621;
x_544 = x_18;
x_545 = x_16;
x_546 = x_17;
x_547 = x_14;
x_548 = x_20;
x_549 = x_610;
x_550 = x_658;
goto block_578;
}
}
}
else
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; 
lean_dec(x_616);
lean_dec(x_614);
lean_dec(x_610);
lean_dec(x_607);
lean_dec(x_605);
lean_dec(x_537);
lean_dec(x_535);
lean_dec(x_530);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_659 = lean_ctor_get(x_619, 0);
lean_inc(x_659);
x_660 = lean_ctor_get(x_619, 1);
lean_inc(x_660);
if (lean_is_exclusive(x_619)) {
 lean_ctor_release(x_619, 0);
 lean_ctor_release(x_619, 1);
 x_661 = x_619;
} else {
 lean_dec_ref(x_619);
 x_661 = lean_box(0);
}
if (lean_is_scalar(x_661)) {
 x_662 = lean_alloc_ctor(1, 2, 0);
} else {
 x_662 = x_661;
}
lean_ctor_set(x_662, 0, x_659);
lean_ctor_set(x_662, 1, x_660);
return x_662;
}
}
else
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; 
lean_dec(x_610);
lean_dec(x_607);
lean_dec(x_605);
lean_dec(x_537);
lean_dec(x_535);
lean_dec(x_530);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_663 = lean_ctor_get(x_611, 0);
lean_inc(x_663);
x_664 = lean_ctor_get(x_611, 1);
lean_inc(x_664);
if (lean_is_exclusive(x_611)) {
 lean_ctor_release(x_611, 0);
 lean_ctor_release(x_611, 1);
 x_665 = x_611;
} else {
 lean_dec_ref(x_611);
 x_665 = lean_box(0);
}
if (lean_is_scalar(x_665)) {
 x_666 = lean_alloc_ctor(1, 2, 0);
} else {
 x_666 = x_665;
}
lean_ctor_set(x_666, 0, x_663);
lean_ctor_set(x_666, 1, x_664);
return x_666;
}
}
else
{
lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; 
lean_dec(x_599);
lean_dec(x_537);
lean_dec(x_535);
lean_dec(x_530);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_667 = lean_ctor_get(x_601, 0);
lean_inc(x_667);
x_668 = lean_ctor_get(x_601, 1);
lean_inc(x_668);
if (lean_is_exclusive(x_601)) {
 lean_ctor_release(x_601, 0);
 lean_ctor_release(x_601, 1);
 x_669 = x_601;
} else {
 lean_dec_ref(x_601);
 x_669 = lean_box(0);
}
if (lean_is_scalar(x_669)) {
 x_670 = lean_alloc_ctor(1, 2, 0);
} else {
 x_670 = x_669;
}
lean_ctor_set(x_670, 0, x_667);
lean_ctor_set(x_670, 1, x_668);
return x_670;
}
}
else
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; 
lean_dec(x_537);
lean_dec(x_535);
lean_dec(x_530);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_671 = lean_ctor_get(x_598, 0);
lean_inc(x_671);
x_672 = lean_ctor_get(x_598, 1);
lean_inc(x_672);
if (lean_is_exclusive(x_598)) {
 lean_ctor_release(x_598, 0);
 lean_ctor_release(x_598, 1);
 x_673 = x_598;
} else {
 lean_dec_ref(x_598);
 x_673 = lean_box(0);
}
if (lean_is_scalar(x_673)) {
 x_674 = lean_alloc_ctor(1, 2, 0);
} else {
 x_674 = x_673;
}
lean_ctor_set(x_674, 0, x_671);
lean_ctor_set(x_674, 1, x_672);
return x_674;
}
}
block_578:
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; 
x_551 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_549, x_548, x_538, x_543);
x_552 = lean_ctor_get(x_551, 0);
lean_inc(x_552);
x_553 = lean_ctor_get(x_551, 1);
lean_inc(x_553);
if (lean_is_exclusive(x_551)) {
 lean_ctor_release(x_551, 0);
 lean_ctor_release(x_551, 1);
 x_554 = x_551;
} else {
 lean_dec_ref(x_551);
 x_554 = lean_box(0);
}
lean_inc(x_538);
lean_inc(x_548);
lean_inc(x_541);
lean_inc(x_552);
x_555 = l_Lean_MVarId_rename(x_539, x_550, x_552, x_544, x_541, x_548, x_538, x_553);
if (lean_obj_tag(x_555) == 0)
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; 
x_556 = lean_ctor_get(x_555, 0);
lean_inc(x_556);
x_557 = lean_ctor_get(x_555, 1);
lean_inc(x_557);
lean_dec(x_555);
x_558 = lean_box(0);
lean_inc(x_556);
if (lean_is_scalar(x_554)) {
 x_559 = lean_alloc_ctor(1, 2, 0);
} else {
 x_559 = x_554;
 lean_ctor_set_tag(x_559, 1);
}
lean_ctor_set(x_559, 0, x_556);
lean_ctor_set(x_559, 1, x_558);
x_560 = l_Lean_Elab_Tactic_setGoals___redArg(x_559, x_540, x_557);
x_561 = lean_ctor_get(x_560, 1);
lean_inc(x_561);
lean_dec(x_560);
x_562 = lean_box(x_10);
x_563 = lean_box(x_9);
x_564 = lean_box(x_12);
lean_inc(x_556);
x_565 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___boxed), 18, 9);
lean_closure_set(x_565, 0, x_556);
lean_closure_set(x_565, 1, x_552);
lean_closure_set(x_565, 2, x_562);
lean_closure_set(x_565, 3, x_563);
lean_closure_set(x_565, 4, x_530);
lean_closure_set(x_565, 5, x_537);
lean_closure_set(x_565, 6, x_11);
lean_closure_set(x_565, 7, x_528);
lean_closure_set(x_565, 8, x_564);
lean_inc(x_538);
lean_inc(x_548);
lean_inc(x_541);
lean_inc(x_546);
lean_inc(x_545);
lean_inc(x_540);
lean_inc(x_547);
x_566 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_withMainContext_spec__0___redArg(x_556, x_565, x_547, x_540, x_545, x_546, x_544, x_541, x_548, x_538, x_561);
if (lean_obj_tag(x_566) == 0)
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; 
x_567 = lean_ctor_get(x_566, 0);
lean_inc(x_567);
x_568 = lean_ctor_get(x_566, 1);
lean_inc(x_568);
lean_dec(x_566);
x_569 = lean_apply_10(x_542, x_567, x_547, x_540, x_545, x_546, x_544, x_541, x_548, x_538, x_568);
return x_569;
}
else
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; 
lean_dec(x_548);
lean_dec(x_547);
lean_dec(x_546);
lean_dec(x_545);
lean_dec(x_544);
lean_dec(x_542);
lean_dec(x_541);
lean_dec(x_540);
lean_dec(x_538);
x_570 = lean_ctor_get(x_566, 0);
lean_inc(x_570);
x_571 = lean_ctor_get(x_566, 1);
lean_inc(x_571);
if (lean_is_exclusive(x_566)) {
 lean_ctor_release(x_566, 0);
 lean_ctor_release(x_566, 1);
 x_572 = x_566;
} else {
 lean_dec_ref(x_566);
 x_572 = lean_box(0);
}
if (lean_is_scalar(x_572)) {
 x_573 = lean_alloc_ctor(1, 2, 0);
} else {
 x_573 = x_572;
}
lean_ctor_set(x_573, 0, x_570);
lean_ctor_set(x_573, 1, x_571);
return x_573;
}
}
else
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; 
lean_dec(x_554);
lean_dec(x_552);
lean_dec(x_548);
lean_dec(x_547);
lean_dec(x_546);
lean_dec(x_545);
lean_dec(x_544);
lean_dec(x_542);
lean_dec(x_541);
lean_dec(x_540);
lean_dec(x_538);
lean_dec(x_537);
lean_dec(x_530);
lean_dec(x_11);
x_574 = lean_ctor_get(x_555, 0);
lean_inc(x_574);
x_575 = lean_ctor_get(x_555, 1);
lean_inc(x_575);
if (lean_is_exclusive(x_555)) {
 lean_ctor_release(x_555, 0);
 lean_ctor_release(x_555, 1);
 x_576 = x_555;
} else {
 lean_dec_ref(x_555);
 x_576 = lean_box(0);
}
if (lean_is_scalar(x_576)) {
 x_577 = lean_alloc_ctor(1, 2, 0);
} else {
 x_577 = x_576;
}
lean_ctor_set(x_577, 0, x_574);
lean_ctor_set(x_577, 1, x_575);
return x_577;
}
}
}
else
{
lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; 
lean_dec(x_526);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_675 = lean_ctor_get(x_529, 0);
lean_inc(x_675);
x_676 = lean_ctor_get(x_529, 1);
lean_inc(x_676);
if (lean_is_exclusive(x_529)) {
 lean_ctor_release(x_529, 0);
 lean_ctor_release(x_529, 1);
 x_677 = x_529;
} else {
 lean_dec_ref(x_529);
 x_677 = lean_box(0);
}
if (lean_is_scalar(x_677)) {
 x_678 = lean_alloc_ctor(1, 2, 0);
} else {
 x_678 = x_677;
}
lean_ctor_set(x_678, 0, x_675);
lean_ctor_set(x_678, 1, x_676);
return x_678;
}
}
}
block_46:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_mk_empty_array_with_capacity(x_5);
x_25 = lean_array_push(x_24, x_23);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_4);
x_26 = l_Lean_Meta_simpGoal(x_2, x_6, x_7, x_8, x_9, x_25, x_4, x_18, x_19, x_20, x_21, x_22);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_27);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_apply_10(x_3, x_4, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_4);
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_35 = l_Lean_MVarId_assumption(x_34, x_18, x_19, x_20, x_21, x_32);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_apply_10(x_3, x_33, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_36);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_33);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 0);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_35);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
x_42 = !lean_is_exclusive(x_26);
if (x_42 == 0)
{
return x_26;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_26, 0);
x_44 = lean_ctor_get(x_26, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_26);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
block_59:
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_box(0);
x_58 = lean_apply_10(x_51, x_57, x_56, x_49, x_53, x_55, x_52, x_48, x_54, x_47, x_50);
return x_58;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, uint8_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
lean_object* x_22; 
x_22 = l_Lean_Elab_Tactic_getMainGoal(x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; lean_object* x_32; lean_object* x_33; size_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_mk_empty_array_with_capacity(x_1);
x_26 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_26);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
lean_inc(x_1);
lean_inc(x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_1);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_26);
x_30 = lean_unsigned_to_nat(5u);
x_31 = lean_usize_of_nat(x_30);
x_32 = lean_usize_to_nat(x_31);
x_33 = lean_nat_pow(x_2, x_32);
lean_dec(x_32);
x_34 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_35 = lean_usize_to_nat(x_34);
x_36 = lean_mk_empty_array_with_capacity(x_35);
lean_dec(x_35);
lean_inc(x_36);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
lean_inc_n(x_1, 2);
x_38 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set(x_38, 2, x_1);
lean_ctor_set(x_38, 3, x_1);
lean_ctor_set_usize(x_38, 4, x_31);
lean_inc(x_27);
x_39 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_39, 0, x_27);
lean_ctor_set(x_39, 1, x_27);
lean_ctor_set(x_39, 2, x_29);
lean_ctor_set(x_39, 3, x_38);
lean_inc(x_39);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_28);
lean_ctor_set(x_40, 1, x_39);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_12);
lean_inc(x_4);
lean_inc(x_3);
x_41 = l_Lean_Meta_simpGoal(x_23, x_3, x_4, x_12, x_5, x_25, x_40, x_17, x_18, x_19, x_20, x_24);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
lean_dec(x_42);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_41, 1);
x_46 = lean_ctor_get(x_41, 0);
lean_dec(x_46);
x_47 = lean_ctor_get(x_19, 2);
lean_inc(x_47);
x_48 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(x_47);
lean_dec(x_47);
if (x_48 == 0)
{
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_ctor_set(x_41, 0, x_39);
return x_41;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_free_object(x_41);
x_49 = lean_ctor_get(x_19, 5);
lean_inc(x_49);
x_50 = l_linter_unnecessarySimpa;
x_51 = lean_mk_string_unchecked("try 'simp' instead of 'simpa'", 29, 29);
x_52 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = l_Lean_MessageData_ofFormat(x_52);
x_54 = l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1(x_50, x_49, x_53, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_45);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_49);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
lean_ctor_set(x_54, 0, x_39);
return x_54;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_39);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_41, 1);
lean_inc(x_59);
lean_dec(x_41);
x_60 = lean_ctor_get(x_19, 2);
lean_inc(x_60);
x_61 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(x_60);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_39);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_63 = lean_ctor_get(x_19, 5);
lean_inc(x_63);
x_64 = l_linter_unnecessarySimpa;
x_65 = lean_mk_string_unchecked("try 'simp' instead of 'simpa'", 29, 29);
x_66 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = l_Lean_MessageData_ofFormat(x_66);
x_68 = l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1(x_64, x_63, x_67, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_59);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_63);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_70 = x_68;
} else {
 lean_dec_ref(x_68);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_39);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_39);
x_72 = lean_ctor_get(x_43, 0);
lean_inc(x_72);
lean_dec(x_43);
x_73 = lean_ctor_get(x_41, 1);
lean_inc(x_73);
lean_dec(x_41);
x_74 = lean_ctor_get(x_42, 1);
lean_inc(x_74);
lean_dec(x_42);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
x_76 = lean_box(x_9);
x_77 = lean_box(x_5);
x_78 = lean_box(x_11);
lean_inc(x_75);
x_79 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___boxed), 22, 13);
lean_closure_set(x_79, 0, x_6);
lean_closure_set(x_79, 1, x_75);
lean_closure_set(x_79, 2, x_7);
lean_closure_set(x_79, 3, x_74);
lean_closure_set(x_79, 4, x_8);
lean_closure_set(x_79, 5, x_3);
lean_closure_set(x_79, 6, x_4);
lean_closure_set(x_79, 7, x_12);
lean_closure_set(x_79, 8, x_76);
lean_closure_set(x_79, 9, x_77);
lean_closure_set(x_79, 10, x_10);
lean_closure_set(x_79, 11, x_78);
lean_closure_set(x_79, 12, x_1);
x_80 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_withMainContext_spec__0___redArg(x_75, x_79, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_73);
return x_80;
}
}
else
{
uint8_t x_81; 
lean_dec(x_39);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_41);
if (x_81 == 0)
{
return x_41;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_41, 0);
x_83 = lean_ctor_get(x_41, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_41);
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
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_22);
if (x_85 == 0)
{
return x_22;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_22, 0);
x_87 = lean_ctor_get(x_22, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_22);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, uint8_t x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29, lean_object* x_30, lean_object* x_31, lean_object* x_32) {
_start:
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_st_ref_get(x_31, x_32);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_101; lean_object* x_102; lean_object* x_115; 
x_35 = lean_ctor_get(x_33, 1);
x_36 = lean_ctor_get(x_33, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_30, 5);
lean_inc(x_37);
x_38 = lean_box(0);
x_51 = lean_unbox(x_38);
x_52 = l_Lean_SourceInfo_fromRef(x_37, x_51);
lean_dec(x_37);
x_53 = lean_mk_string_unchecked("simp", 4, 4);
lean_inc(x_53);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_54 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_53);
lean_inc(x_52);
lean_ctor_set_tag(x_33, 2);
lean_ctor_set(x_33, 1, x_53);
lean_ctor_set(x_33, 0, x_52);
x_55 = lean_mk_string_unchecked("null", 4, 4);
x_56 = l_Lean_Name_mkStr1(x_55);
x_57 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_125; 
x_125 = l_Array_empty(lean_box(0));
x_115 = x_125;
goto block_124;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_23, 0);
lean_inc(x_126);
lean_dec(x_23);
x_127 = l_Array_empty(lean_box(0));
x_128 = lean_array_push(x_127, x_126);
x_115 = x_128;
goto block_124;
}
block_50:
{
uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_unbox(x_38);
x_45 = l_Lean_Meta_Simp_Context_setFailIfUnchanged(x_43, x_44);
lean_dec(x_43);
x_46 = lean_box(x_7);
x_47 = lean_box(x_19);
x_48 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__7___boxed), 21, 11);
lean_closure_set(x_48, 0, x_11);
lean_closure_set(x_48, 1, x_16);
lean_closure_set(x_48, 2, x_45);
lean_closure_set(x_48, 3, x_41);
lean_closure_set(x_48, 4, x_46);
lean_closure_set(x_48, 5, x_17);
lean_closure_set(x_48, 6, x_40);
lean_closure_set(x_48, 7, x_14);
lean_closure_set(x_48, 8, x_38);
lean_closure_set(x_48, 9, x_10);
lean_closure_set(x_48, 10, x_47);
x_49 = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(x_42, x_48, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_39);
lean_dec(x_42);
return x_49;
}
block_66:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_box(x_7);
x_64 = lean_box(x_19);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_11);
lean_inc(x_10);
x_65 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___boxed), 33, 23);
lean_closure_set(x_65, 0, x_5);
lean_closure_set(x_65, 1, x_57);
lean_closure_set(x_65, 2, x_56);
lean_closure_set(x_65, 3, x_6);
lean_closure_set(x_65, 4, x_1);
lean_closure_set(x_65, 5, x_2);
lean_closure_set(x_65, 6, x_3);
lean_closure_set(x_65, 7, x_63);
lean_closure_set(x_65, 8, x_8);
lean_closure_set(x_65, 9, x_38);
lean_closure_set(x_65, 10, x_9);
lean_closure_set(x_65, 11, x_10);
lean_closure_set(x_65, 12, x_11);
lean_closure_set(x_65, 13, x_12);
lean_closure_set(x_65, 14, x_13);
lean_closure_set(x_65, 15, x_14);
lean_closure_set(x_65, 16, x_58);
lean_closure_set(x_65, 17, x_54);
lean_closure_set(x_65, 18, x_15);
lean_closure_set(x_65, 19, x_16);
lean_closure_set(x_65, 20, x_17);
lean_closure_set(x_65, 21, x_18);
lean_closure_set(x_65, 22, x_64);
x_39 = x_62;
x_40 = x_65;
x_41 = x_60;
x_42 = x_61;
x_43 = x_59;
goto block_50;
}
block_100:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_inc(x_57);
x_70 = l_Array_append(lean_box(0), x_57, x_69);
lean_dec(x_69);
lean_inc(x_56);
lean_inc(x_52);
x_71 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_71, 0, x_52);
lean_ctor_set(x_71, 1, x_56);
lean_ctor_set(x_71, 2, x_70);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_52);
x_72 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_72, 0, x_52);
lean_ctor_set(x_72, 1, x_56);
lean_ctor_set(x_72, 2, x_57);
lean_inc(x_54);
x_73 = l_Lean_Syntax_node6(x_52, x_54, x_33, x_4, x_68, x_67, x_71, x_72);
x_74 = lean_box(0);
x_75 = lean_alloc_closure((void*)(l_Lean_Meta_getSimpTheorems___boxed), 3, 0);
lean_inc(x_73);
x_76 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(x_76, 0, x_73);
lean_closure_set(x_76, 1, x_38);
lean_closure_set(x_76, 2, x_74);
lean_closure_set(x_76, 3, x_38);
lean_closure_set(x_76, 4, x_75);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
x_77 = l_Lean_Elab_Tactic_withMainContext___redArg(x_76, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_35);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_78, 2);
lean_inc(x_82);
lean_dec(x_78);
x_58 = x_73;
x_59 = x_80;
x_60 = x_81;
x_61 = x_82;
x_62 = x_79;
goto block_66;
}
else
{
if (x_19 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_77, 1);
lean_inc(x_83);
lean_dec(x_77);
x_84 = lean_ctor_get(x_78, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_78, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_78, 2);
lean_inc(x_86);
lean_dec(x_78);
x_58 = x_73;
x_59 = x_84;
x_60 = x_85;
x_61 = x_86;
x_62 = x_83;
goto block_66;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_87 = lean_ctor_get(x_77, 1);
lean_inc(x_87);
lean_dec(x_77);
x_88 = lean_ctor_get(x_78, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_78, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_78, 2);
lean_inc(x_90);
lean_dec(x_78);
x_91 = lean_box(x_7);
x_92 = lean_box(x_19);
x_93 = lean_box(x_19);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_11);
lean_inc(x_10);
x_94 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___boxed), 33, 23);
lean_closure_set(x_94, 0, x_5);
lean_closure_set(x_94, 1, x_57);
lean_closure_set(x_94, 2, x_56);
lean_closure_set(x_94, 3, x_6);
lean_closure_set(x_94, 4, x_1);
lean_closure_set(x_94, 5, x_2);
lean_closure_set(x_94, 6, x_3);
lean_closure_set(x_94, 7, x_91);
lean_closure_set(x_94, 8, x_8);
lean_closure_set(x_94, 9, x_92);
lean_closure_set(x_94, 10, x_9);
lean_closure_set(x_94, 11, x_10);
lean_closure_set(x_94, 12, x_11);
lean_closure_set(x_94, 13, x_12);
lean_closure_set(x_94, 14, x_13);
lean_closure_set(x_94, 15, x_14);
lean_closure_set(x_94, 16, x_73);
lean_closure_set(x_94, 17, x_54);
lean_closure_set(x_94, 18, x_15);
lean_closure_set(x_94, 19, x_16);
lean_closure_set(x_94, 20, x_17);
lean_closure_set(x_94, 21, x_18);
lean_closure_set(x_94, 22, x_93);
x_95 = l_Lean_Meta_Simp_Context_setAutoUnfold(x_88);
lean_dec(x_88);
x_39 = x_87;
x_40 = x_94;
x_41 = x_89;
x_42 = x_90;
x_43 = x_95;
goto block_50;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_73);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_77);
if (x_96 == 0)
{
return x_77;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_77, 0);
x_98 = lean_ctor_get(x_77, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_77);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
block_114:
{
lean_object* x_103; lean_object* x_104; 
lean_inc(x_57);
x_103 = l_Array_append(lean_box(0), x_57, x_102);
lean_dec(x_102);
lean_inc(x_56);
lean_inc(x_52);
x_104 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_104, 0, x_52);
lean_ctor_set(x_104, 1, x_56);
lean_ctor_set(x_104, 2, x_103);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_105; 
x_105 = l_Array_empty(lean_box(0));
x_67 = x_104;
x_68 = x_101;
x_69 = x_105;
goto block_100;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_106 = lean_ctor_get(x_21, 0);
x_107 = lean_mk_string_unchecked("[", 1, 1);
lean_inc(x_52);
x_108 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_108, 0, x_52);
lean_ctor_set(x_108, 1, x_107);
lean_inc(x_57);
x_109 = l_Array_append(lean_box(0), x_57, x_106);
lean_inc(x_56);
lean_inc(x_52);
x_110 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_110, 0, x_52);
lean_ctor_set(x_110, 1, x_56);
lean_ctor_set(x_110, 2, x_109);
x_111 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_52);
x_112 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_112, 0, x_52);
lean_ctor_set(x_112, 1, x_111);
x_113 = l_Array_mkArray3(lean_box(0), x_108, x_110, x_112);
x_67 = x_104;
x_68 = x_101;
x_69 = x_113;
goto block_100;
}
}
block_124:
{
lean_object* x_116; lean_object* x_117; 
lean_inc(x_57);
x_116 = l_Array_append(lean_box(0), x_57, x_115);
lean_dec(x_115);
lean_inc(x_56);
lean_inc(x_52);
x_117 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_117, 0, x_52);
lean_ctor_set(x_117, 1, x_56);
lean_ctor_set(x_117, 2, x_116);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_118; 
x_118 = l_Array_empty(lean_box(0));
x_101 = x_117;
x_102 = x_118;
goto block_114;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_119 = lean_ctor_get(x_22, 0);
x_120 = l_Lean_SourceInfo_fromRef(x_119, x_7);
x_121 = lean_mk_string_unchecked("only", 4, 4);
x_122 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = l_Array_mkArray1___redArg(x_122);
x_101 = x_117;
x_102 = x_123;
goto block_114;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_195; lean_object* x_196; lean_object* x_209; 
x_129 = lean_ctor_get(x_33, 1);
lean_inc(x_129);
lean_dec(x_33);
x_130 = lean_ctor_get(x_30, 5);
lean_inc(x_130);
x_131 = lean_box(0);
x_144 = lean_unbox(x_131);
x_145 = l_Lean_SourceInfo_fromRef(x_130, x_144);
lean_dec(x_130);
x_146 = lean_mk_string_unchecked("simp", 4, 4);
lean_inc(x_146);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_147 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_146);
lean_inc(x_145);
x_148 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_146);
x_149 = lean_mk_string_unchecked("null", 4, 4);
x_150 = l_Lean_Name_mkStr1(x_149);
x_151 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_219; 
x_219 = l_Array_empty(lean_box(0));
x_209 = x_219;
goto block_218;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_23, 0);
lean_inc(x_220);
lean_dec(x_23);
x_221 = l_Array_empty(lean_box(0));
x_222 = lean_array_push(x_221, x_220);
x_209 = x_222;
goto block_218;
}
block_143:
{
uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_137 = lean_unbox(x_131);
x_138 = l_Lean_Meta_Simp_Context_setFailIfUnchanged(x_136, x_137);
lean_dec(x_136);
x_139 = lean_box(x_7);
x_140 = lean_box(x_19);
x_141 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__7___boxed), 21, 11);
lean_closure_set(x_141, 0, x_11);
lean_closure_set(x_141, 1, x_16);
lean_closure_set(x_141, 2, x_138);
lean_closure_set(x_141, 3, x_134);
lean_closure_set(x_141, 4, x_139);
lean_closure_set(x_141, 5, x_17);
lean_closure_set(x_141, 6, x_133);
lean_closure_set(x_141, 7, x_14);
lean_closure_set(x_141, 8, x_131);
lean_closure_set(x_141, 9, x_10);
lean_closure_set(x_141, 10, x_140);
x_142 = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(x_135, x_141, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_132);
lean_dec(x_135);
return x_142;
}
block_160:
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_box(x_7);
x_158 = lean_box(x_19);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_11);
lean_inc(x_10);
x_159 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___boxed), 33, 23);
lean_closure_set(x_159, 0, x_5);
lean_closure_set(x_159, 1, x_151);
lean_closure_set(x_159, 2, x_150);
lean_closure_set(x_159, 3, x_6);
lean_closure_set(x_159, 4, x_1);
lean_closure_set(x_159, 5, x_2);
lean_closure_set(x_159, 6, x_3);
lean_closure_set(x_159, 7, x_157);
lean_closure_set(x_159, 8, x_8);
lean_closure_set(x_159, 9, x_131);
lean_closure_set(x_159, 10, x_9);
lean_closure_set(x_159, 11, x_10);
lean_closure_set(x_159, 12, x_11);
lean_closure_set(x_159, 13, x_12);
lean_closure_set(x_159, 14, x_13);
lean_closure_set(x_159, 15, x_14);
lean_closure_set(x_159, 16, x_152);
lean_closure_set(x_159, 17, x_147);
lean_closure_set(x_159, 18, x_15);
lean_closure_set(x_159, 19, x_16);
lean_closure_set(x_159, 20, x_17);
lean_closure_set(x_159, 21, x_18);
lean_closure_set(x_159, 22, x_158);
x_132 = x_156;
x_133 = x_159;
x_134 = x_154;
x_135 = x_155;
x_136 = x_153;
goto block_143;
}
block_194:
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_inc(x_151);
x_164 = l_Array_append(lean_box(0), x_151, x_163);
lean_dec(x_163);
lean_inc(x_150);
lean_inc(x_145);
x_165 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_165, 0, x_145);
lean_ctor_set(x_165, 1, x_150);
lean_ctor_set(x_165, 2, x_164);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_145);
x_166 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_166, 0, x_145);
lean_ctor_set(x_166, 1, x_150);
lean_ctor_set(x_166, 2, x_151);
lean_inc(x_147);
x_167 = l_Lean_Syntax_node6(x_145, x_147, x_148, x_4, x_162, x_161, x_165, x_166);
x_168 = lean_box(0);
x_169 = lean_alloc_closure((void*)(l_Lean_Meta_getSimpTheorems___boxed), 3, 0);
lean_inc(x_167);
x_170 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(x_170, 0, x_167);
lean_closure_set(x_170, 1, x_131);
lean_closure_set(x_170, 2, x_168);
lean_closure_set(x_170, 3, x_131);
lean_closure_set(x_170, 4, x_169);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
x_171 = l_Lean_Elab_Tactic_withMainContext___redArg(x_170, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_129);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = lean_ctor_get(x_172, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_172, 1);
lean_inc(x_175);
x_176 = lean_ctor_get(x_172, 2);
lean_inc(x_176);
lean_dec(x_172);
x_152 = x_167;
x_153 = x_174;
x_154 = x_175;
x_155 = x_176;
x_156 = x_173;
goto block_160;
}
else
{
if (x_19 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_177 = lean_ctor_get(x_171, 1);
lean_inc(x_177);
lean_dec(x_171);
x_178 = lean_ctor_get(x_172, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_172, 1);
lean_inc(x_179);
x_180 = lean_ctor_get(x_172, 2);
lean_inc(x_180);
lean_dec(x_172);
x_152 = x_167;
x_153 = x_178;
x_154 = x_179;
x_155 = x_180;
x_156 = x_177;
goto block_160;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_181 = lean_ctor_get(x_171, 1);
lean_inc(x_181);
lean_dec(x_171);
x_182 = lean_ctor_get(x_172, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_172, 1);
lean_inc(x_183);
x_184 = lean_ctor_get(x_172, 2);
lean_inc(x_184);
lean_dec(x_172);
x_185 = lean_box(x_7);
x_186 = lean_box(x_19);
x_187 = lean_box(x_19);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_11);
lean_inc(x_10);
x_188 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___boxed), 33, 23);
lean_closure_set(x_188, 0, x_5);
lean_closure_set(x_188, 1, x_151);
lean_closure_set(x_188, 2, x_150);
lean_closure_set(x_188, 3, x_6);
lean_closure_set(x_188, 4, x_1);
lean_closure_set(x_188, 5, x_2);
lean_closure_set(x_188, 6, x_3);
lean_closure_set(x_188, 7, x_185);
lean_closure_set(x_188, 8, x_8);
lean_closure_set(x_188, 9, x_186);
lean_closure_set(x_188, 10, x_9);
lean_closure_set(x_188, 11, x_10);
lean_closure_set(x_188, 12, x_11);
lean_closure_set(x_188, 13, x_12);
lean_closure_set(x_188, 14, x_13);
lean_closure_set(x_188, 15, x_14);
lean_closure_set(x_188, 16, x_167);
lean_closure_set(x_188, 17, x_147);
lean_closure_set(x_188, 18, x_15);
lean_closure_set(x_188, 19, x_16);
lean_closure_set(x_188, 20, x_17);
lean_closure_set(x_188, 21, x_18);
lean_closure_set(x_188, 22, x_187);
x_189 = l_Lean_Meta_Simp_Context_setAutoUnfold(x_182);
lean_dec(x_182);
x_132 = x_181;
x_133 = x_188;
x_134 = x_183;
x_135 = x_184;
x_136 = x_189;
goto block_143;
}
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_167);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_147);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_190 = lean_ctor_get(x_171, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_171, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_192 = x_171;
} else {
 lean_dec_ref(x_171);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(1, 2, 0);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_190);
lean_ctor_set(x_193, 1, x_191);
return x_193;
}
}
block_208:
{
lean_object* x_197; lean_object* x_198; 
lean_inc(x_151);
x_197 = l_Array_append(lean_box(0), x_151, x_196);
lean_dec(x_196);
lean_inc(x_150);
lean_inc(x_145);
x_198 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_198, 0, x_145);
lean_ctor_set(x_198, 1, x_150);
lean_ctor_set(x_198, 2, x_197);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_199; 
x_199 = l_Array_empty(lean_box(0));
x_161 = x_198;
x_162 = x_195;
x_163 = x_199;
goto block_194;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_200 = lean_ctor_get(x_21, 0);
x_201 = lean_mk_string_unchecked("[", 1, 1);
lean_inc(x_145);
x_202 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_202, 0, x_145);
lean_ctor_set(x_202, 1, x_201);
lean_inc(x_151);
x_203 = l_Array_append(lean_box(0), x_151, x_200);
lean_inc(x_150);
lean_inc(x_145);
x_204 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_204, 0, x_145);
lean_ctor_set(x_204, 1, x_150);
lean_ctor_set(x_204, 2, x_203);
x_205 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_145);
x_206 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_206, 0, x_145);
lean_ctor_set(x_206, 1, x_205);
x_207 = l_Array_mkArray3(lean_box(0), x_202, x_204, x_206);
x_161 = x_198;
x_162 = x_195;
x_163 = x_207;
goto block_194;
}
}
block_218:
{
lean_object* x_210; lean_object* x_211; 
lean_inc(x_151);
x_210 = l_Array_append(lean_box(0), x_151, x_209);
lean_dec(x_209);
lean_inc(x_150);
lean_inc(x_145);
x_211 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_211, 0, x_145);
lean_ctor_set(x_211, 1, x_150);
lean_ctor_set(x_211, 2, x_210);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_212; 
x_212 = l_Array_empty(lean_box(0));
x_195 = x_211;
x_196 = x_212;
goto block_208;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_213 = lean_ctor_get(x_22, 0);
x_214 = l_Lean_SourceInfo_fromRef(x_213, x_7);
x_215 = lean_mk_string_unchecked("only", 4, 4);
x_216 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
x_217 = l_Array_mkArray1___redArg(x_216);
x_195 = x_211;
x_196 = x_217;
goto block_208;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_mk_string_unchecked("Lean", 4, 4);
x_12 = lean_mk_string_unchecked("Parser", 6, 6);
x_13 = lean_mk_string_unchecked("Tactic", 6, 6);
x_14 = lean_mk_string_unchecked("simpa", 5, 5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_15 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_14);
lean_inc(x_1);
x_16 = l_Lean_Syntax_isOfKind(x_1, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
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
x_17 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_10);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_196; uint8_t x_197; 
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__0___boxed), 9, 0);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_unsigned_to_nat(1u);
x_196 = l_Lean_Syntax_getArg(x_1, x_20);
x_197 = l_Lean_Syntax_isNone(x_196);
if (x_197 == 0)
{
uint8_t x_198; 
lean_inc(x_196);
x_198 = l_Lean_Syntax_matchesNull(x_196, x_20);
if (x_198 == 0)
{
lean_object* x_199; 
lean_dec(x_196);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
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
x_199 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_10);
return x_199;
}
else
{
lean_object* x_200; lean_object* x_201; 
x_200 = l_Lean_Syntax_getArg(x_196, x_19);
lean_dec(x_196);
x_201 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_201, 0, x_200);
x_177 = x_201;
x_178 = x_2;
x_179 = x_3;
x_180 = x_4;
x_181 = x_5;
x_182 = x_6;
x_183 = x_7;
x_184 = x_8;
x_185 = x_9;
x_186 = x_10;
goto block_195;
}
}
else
{
lean_object* x_202; 
lean_dec(x_196);
x_202 = lean_box(0);
x_177 = x_202;
x_178 = x_2;
x_179 = x_3;
x_180 = x_4;
x_181 = x_5;
x_182 = x_6;
x_183 = x_7;
x_184 = x_8;
x_185 = x_9;
x_186 = x_10;
goto block_195;
}
block_49:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = l_Lean_Syntax_getArg(x_1, x_19);
lean_dec(x_1);
x_44 = lean_box(x_16);
x_45 = lean_box(x_26);
x_46 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__8___boxed), 32, 23);
lean_closure_set(x_46, 0, x_11);
lean_closure_set(x_46, 1, x_12);
lean_closure_set(x_46, 2, x_13);
lean_closure_set(x_46, 3, x_27);
lean_closure_set(x_46, 4, x_43);
lean_closure_set(x_46, 5, x_28);
lean_closure_set(x_46, 6, x_44);
lean_closure_set(x_46, 7, x_15);
lean_closure_set(x_46, 8, x_18);
lean_closure_set(x_46, 9, x_14);
lean_closure_set(x_46, 10, x_19);
lean_closure_set(x_46, 11, x_33);
lean_closure_set(x_46, 12, x_34);
lean_closure_set(x_46, 13, x_20);
lean_closure_set(x_46, 14, x_23);
lean_closure_set(x_46, 15, x_37);
lean_closure_set(x_46, 16, x_41);
lean_closure_set(x_46, 17, x_39);
lean_closure_set(x_46, 18, x_45);
lean_closure_set(x_46, 19, x_29);
lean_closure_set(x_46, 20, x_40);
lean_closure_set(x_46, 21, x_32);
lean_closure_set(x_46, 22, x_42);
x_47 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics), 10, 1);
lean_closure_set(x_47, 0, x_46);
x_48 = l_Lean_Elab_Tactic_focus(lean_box(0), x_47, x_24, x_22, x_21, x_35, x_36, x_38, x_25, x_31, x_30);
return x_48;
}
block_77:
{
lean_object* x_72; 
x_72 = l_Lean_Syntax_getOptional_x3f(x_52);
lean_dec(x_52);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
x_73 = lean_box(0);
x_21 = x_50;
x_22 = x_51;
x_23 = x_53;
x_24 = x_54;
x_25 = x_55;
x_26 = x_56;
x_27 = x_57;
x_28 = x_58;
x_29 = x_59;
x_30 = x_60;
x_31 = x_61;
x_32 = x_62;
x_33 = x_64;
x_34 = x_63;
x_35 = x_65;
x_36 = x_66;
x_37 = x_67;
x_38 = x_69;
x_39 = x_68;
x_40 = x_70;
x_41 = x_71;
x_42 = x_73;
goto block_49;
}
else
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_72);
if (x_74 == 0)
{
x_21 = x_50;
x_22 = x_51;
x_23 = x_53;
x_24 = x_54;
x_25 = x_55;
x_26 = x_56;
x_27 = x_57;
x_28 = x_58;
x_29 = x_59;
x_30 = x_60;
x_31 = x_61;
x_32 = x_62;
x_33 = x_64;
x_34 = x_63;
x_35 = x_65;
x_36 = x_66;
x_37 = x_67;
x_38 = x_69;
x_39 = x_68;
x_40 = x_70;
x_41 = x_71;
x_42 = x_72;
goto block_49;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_72, 0);
lean_inc(x_75);
lean_dec(x_72);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_21 = x_50;
x_22 = x_51;
x_23 = x_53;
x_24 = x_54;
x_25 = x_55;
x_26 = x_56;
x_27 = x_57;
x_28 = x_58;
x_29 = x_59;
x_30 = x_60;
x_31 = x_61;
x_32 = x_62;
x_33 = x_64;
x_34 = x_63;
x_35 = x_65;
x_36 = x_66;
x_37 = x_67;
x_38 = x_69;
x_39 = x_68;
x_40 = x_70;
x_41 = x_71;
x_42 = x_76;
goto block_49;
}
}
}
block_108:
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_100 = lean_unsigned_to_nat(4u);
x_101 = l_Lean_Syntax_getArg(x_92, x_100);
lean_dec(x_92);
x_102 = l_Lean_Syntax_isNone(x_101);
if (x_102 == 0)
{
uint8_t x_103; 
lean_inc(x_101);
x_103 = l_Lean_Syntax_matchesNull(x_101, x_82);
lean_dec(x_82);
if (x_103 == 0)
{
lean_object* x_104; 
lean_dec(x_101);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_104 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_89);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = l_Lean_Syntax_getArg(x_101, x_20);
lean_dec(x_101);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
x_50 = x_78;
x_51 = x_79;
x_52 = x_80;
x_53 = x_81;
x_54 = x_83;
x_55 = x_84;
x_56 = x_85;
x_57 = x_86;
x_58 = x_87;
x_59 = x_88;
x_60 = x_89;
x_61 = x_90;
x_62 = x_91;
x_63 = x_93;
x_64 = x_100;
x_65 = x_94;
x_66 = x_95;
x_67 = x_96;
x_68 = x_98;
x_69 = x_97;
x_70 = x_99;
x_71 = x_106;
goto block_77;
}
}
else
{
lean_object* x_107; 
lean_dec(x_101);
lean_dec(x_82);
x_107 = lean_box(0);
x_50 = x_78;
x_51 = x_79;
x_52 = x_80;
x_53 = x_81;
x_54 = x_83;
x_55 = x_84;
x_56 = x_85;
x_57 = x_86;
x_58 = x_87;
x_59 = x_88;
x_60 = x_89;
x_61 = x_90;
x_62 = x_91;
x_63 = x_93;
x_64 = x_100;
x_65 = x_94;
x_66 = x_95;
x_67 = x_96;
x_68 = x_98;
x_69 = x_97;
x_70 = x_99;
x_71 = x_107;
goto block_77;
}
}
block_144:
{
lean_object* x_131; uint8_t x_132; 
x_131 = l_Lean_Syntax_getArg(x_120, x_117);
lean_dec(x_117);
x_132 = l_Lean_Syntax_isNone(x_131);
if (x_132 == 0)
{
uint8_t x_133; 
lean_inc(x_131);
x_133 = l_Lean_Syntax_matchesNull(x_131, x_20);
if (x_133 == 0)
{
lean_object* x_134; 
lean_dec(x_131);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_134 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_130);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_135 = l_Lean_Syntax_getArg(x_131, x_19);
lean_dec(x_131);
x_136 = lean_mk_string_unchecked("simpArgs", 8, 8);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_137 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_136);
lean_inc(x_135);
x_138 = l_Lean_Syntax_isOfKind(x_135, x_137);
lean_dec(x_137);
if (x_138 == 0)
{
lean_object* x_139; 
lean_dec(x_135);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_139 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_130);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = l_Lean_Syntax_getArg(x_135, x_20);
lean_dec(x_135);
x_141 = l_Lean_Syntax_getArgs(x_140);
lean_dec(x_140);
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_141);
x_78 = x_124;
x_79 = x_123;
x_80 = x_118;
x_81 = x_109;
x_82 = x_119;
x_83 = x_122;
x_84 = x_128;
x_85 = x_111;
x_86 = x_112;
x_87 = x_114;
x_88 = x_113;
x_89 = x_130;
x_90 = x_129;
x_91 = x_121;
x_92 = x_120;
x_93 = x_110;
x_94 = x_125;
x_95 = x_126;
x_96 = x_115;
x_97 = x_127;
x_98 = x_116;
x_99 = x_142;
goto block_108;
}
}
}
else
{
lean_object* x_143; 
lean_dec(x_131);
x_143 = lean_box(0);
x_78 = x_124;
x_79 = x_123;
x_80 = x_118;
x_81 = x_109;
x_82 = x_119;
x_83 = x_122;
x_84 = x_128;
x_85 = x_111;
x_86 = x_112;
x_87 = x_114;
x_88 = x_113;
x_89 = x_130;
x_90 = x_129;
x_91 = x_121;
x_92 = x_120;
x_93 = x_110;
x_94 = x_125;
x_95 = x_126;
x_96 = x_115;
x_97 = x_127;
x_98 = x_116;
x_99 = x_143;
goto block_108;
}
}
block_176:
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_157 = lean_unsigned_to_nat(3u);
x_158 = l_Lean_Syntax_getArg(x_1, x_157);
x_159 = lean_mk_string_unchecked("simpaArgsRest", 13, 13);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_160 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_159);
lean_inc(x_158);
x_161 = l_Lean_Syntax_isOfKind(x_158, x_160);
if (x_161 == 0)
{
lean_object* x_162; 
lean_dec(x_160);
lean_dec(x_158);
lean_dec(x_156);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_162 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_155);
return x_162;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_163 = l_Lean_Syntax_getArg(x_158, x_19);
x_164 = lean_mk_string_unchecked("optConfig", 9, 9);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_165 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_164);
lean_inc(x_163);
x_166 = l_Lean_Syntax_isOfKind(x_163, x_165);
if (x_166 == 0)
{
lean_object* x_167; 
lean_dec(x_165);
lean_dec(x_163);
lean_dec(x_160);
lean_dec(x_158);
lean_dec(x_156);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_167 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_155);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_168 = l_Lean_Syntax_getArg(x_158, x_20);
x_169 = l_Lean_Syntax_getArg(x_158, x_153);
x_170 = l_Lean_Syntax_isNone(x_169);
if (x_170 == 0)
{
uint8_t x_171; 
lean_inc(x_169);
x_171 = l_Lean_Syntax_matchesNull(x_169, x_20);
if (x_171 == 0)
{
lean_object* x_172; 
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_165);
lean_dec(x_163);
lean_dec(x_160);
lean_dec(x_158);
lean_dec(x_156);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_172 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_155);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; 
x_173 = l_Lean_Syntax_getArg(x_169, x_19);
lean_dec(x_169);
x_174 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_174, 0, x_173);
lean_inc(x_153);
x_109 = x_165;
x_110 = x_157;
x_111 = x_166;
x_112 = x_163;
x_113 = x_156;
x_114 = x_160;
x_115 = x_153;
x_116 = x_154;
x_117 = x_157;
x_118 = x_168;
x_119 = x_153;
x_120 = x_158;
x_121 = x_174;
x_122 = x_146;
x_123 = x_149;
x_124 = x_145;
x_125 = x_152;
x_126 = x_148;
x_127 = x_147;
x_128 = x_150;
x_129 = x_151;
x_130 = x_155;
goto block_144;
}
}
else
{
lean_object* x_175; 
lean_dec(x_169);
x_175 = lean_box(0);
lean_inc(x_153);
x_109 = x_165;
x_110 = x_157;
x_111 = x_166;
x_112 = x_163;
x_113 = x_156;
x_114 = x_160;
x_115 = x_153;
x_116 = x_154;
x_117 = x_157;
x_118 = x_168;
x_119 = x_153;
x_120 = x_158;
x_121 = x_175;
x_122 = x_146;
x_123 = x_149;
x_124 = x_145;
x_125 = x_152;
x_126 = x_148;
x_127 = x_147;
x_128 = x_150;
x_129 = x_151;
x_130 = x_155;
goto block_144;
}
}
}
}
block_195:
{
lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_187 = lean_unsigned_to_nat(2u);
x_188 = l_Lean_Syntax_getArg(x_1, x_187);
x_189 = l_Lean_Syntax_isNone(x_188);
if (x_189 == 0)
{
uint8_t x_190; 
lean_inc(x_188);
x_190 = l_Lean_Syntax_matchesNull(x_188, x_20);
if (x_190 == 0)
{
lean_object* x_191; 
lean_dec(x_188);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_191 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_186);
return x_191;
}
else
{
lean_object* x_192; lean_object* x_193; 
x_192 = l_Lean_Syntax_getArg(x_188, x_19);
lean_dec(x_188);
x_193 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_193, 0, x_192);
x_145 = x_180;
x_146 = x_178;
x_147 = x_183;
x_148 = x_182;
x_149 = x_179;
x_150 = x_184;
x_151 = x_185;
x_152 = x_181;
x_153 = x_187;
x_154 = x_177;
x_155 = x_186;
x_156 = x_193;
goto block_176;
}
}
else
{
lean_object* x_194; 
lean_dec(x_188);
x_194 = lean_box(0);
x_145 = x_180;
x_146 = x_178;
x_147 = x_183;
x_148 = x_182;
x_149 = x_179;
x_150 = x_184;
x_151 = x_185;
x_152 = x_181;
x_153 = x_187;
x_154 = x_177;
x_155 = x_186;
x_156 = x_194;
goto block_176;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getExprMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3_spec__3___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_getExprMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getDelayedMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3_spec__4___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_getDelayedMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_5);
lean_dec(x_5);
x_17 = l_Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3___lam__0(x_1, x_2, x_3, x_4, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___boxed(lean_object** _args) {
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
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
lean_object* x_27 = _args[26];
lean_object* x_28 = _args[27];
lean_object* x_29 = _args[28];
lean_object* x_30 = _args[29];
lean_object* x_31 = _args[30];
lean_object* x_32 = _args[31];
lean_object* x_33 = _args[32];
_start:
{
uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_34 = lean_unbox(x_8);
lean_dec(x_8);
x_35 = lean_unbox(x_10);
lean_dec(x_10);
x_36 = lean_unbox(x_23);
lean_dec(x_23);
x_37 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_34, x_9, x_35, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_36, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_1);
return x_37;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___boxed(lean_object** _args) {
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
_start:
{
uint8_t x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_19 = lean_unbox(x_3);
lean_dec(x_3);
x_20 = lean_unbox(x_4);
lean_dec(x_4);
x_21 = lean_unbox(x_9);
lean_dec(x_9);
x_22 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4(x_1, x_2, x_19, x_20, x_5, x_6, x_7, x_8, x_21, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___boxed(lean_object** _args) {
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
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
_start:
{
uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; 
x_23 = lean_unbox(x_9);
lean_dec(x_9);
x_24 = lean_unbox(x_10);
lean_dec(x_10);
x_25 = lean_unbox(x_12);
lean_dec(x_12);
x_26 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_23, x_24, x_11, x_25, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
lean_dec(x_13);
lean_dec(x_5);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__7___boxed(lean_object** _args) {
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
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
_start:
{
uint8_t x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; 
x_22 = lean_unbox(x_5);
lean_dec(x_5);
x_23 = lean_unbox(x_9);
lean_dec(x_9);
x_24 = lean_unbox(x_11);
lean_dec(x_11);
x_25 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__7(x_1, x_2, x_3, x_4, x_22, x_6, x_7, x_8, x_23, x_10, x_24, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_17);
lean_dec(x_2);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__8___boxed(lean_object** _args) {
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
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
lean_object* x_27 = _args[26];
lean_object* x_28 = _args[27];
lean_object* x_29 = _args[28];
lean_object* x_30 = _args[29];
lean_object* x_31 = _args[30];
lean_object* x_32 = _args[31];
_start:
{
uint8_t x_33; uint8_t x_34; lean_object* x_35; 
x_33 = lean_unbox(x_7);
lean_dec(x_7);
x_34 = lean_unbox(x_19);
lean_dec(x_19);
x_35 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__8(x_1, x_2, x_3, x_4, x_5, x_6, x_33, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_34, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
return x_35;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("simpa", 5, 5);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("Simpa", 5, 5);
x_10 = lean_mk_string_unchecked("evalSimpa", 9, 9);
x_11 = l_Lean_Name_mkStr5(x_3, x_8, x_5, x_9, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa), 10, 0);
x_13 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_11, x_12, x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("Simpa", 5, 5);
x_6 = lean_mk_string_unchecked("evalSimpa", 9, 9);
x_7 = l_Lean_Name_mkStr5(x_2, x_3, x_4, x_5, x_6);
x_8 = lean_unsigned_to_nat(31u);
x_9 = lean_unsigned_to_nat(43u);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_unsigned_to_nat(90u);
x_12 = lean_unsigned_to_nat(33u);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set(x_14, 3, x_12);
x_15 = lean_unsigned_to_nat(47u);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_unsigned_to_nat(56u);
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
lean_object* initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_App(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Linter_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Simpa(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Assumption(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_TryThis(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_App(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_linter_unnecessarySimpa = lean_io_result_get_value(res);
lean_mark_persistent(l_linter_unnecessarySimpa);
lean_dec_ref(res);
l_Lean_Elab_Tactic_Simpa_instReprUseImplicitLambdaResult = _init_l_Lean_Elab_Tactic_Simpa_instReprUseImplicitLambdaResult();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_instReprUseImplicitLambdaResult);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
